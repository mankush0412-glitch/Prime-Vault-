import asyncio
import logging
import time
import aiohttp


class Server3Server:
    """HeartTGStore API integration used as the bot's Server 3.

    The supplier exposes two upstream pools. In this bot they are deliberately
    named Provider 1 and Provider 2 in every user/admin-facing surface:
      - Provider 1 = supplier `server: 1` / Main Server
      - Provider 2 = supplier `server: 2`

    Only OTP delivery is exposed to customers. Session-file endpoints are not
    used automatically because fetching a Provider 1 session can end refund
    eligibility for a waiting OTP order.
    """

    TEMPORARY_CODES = {
        "SERVER_BUSY",
        "SERVER_UNAVAILABLE",
        "SERVER_DISABLED",
        "API_DISABLED",
        "VERIFY_UNAVAILABLE",
        "RATE_LIMIT_EXCEEDED",
        "LISTENER_LIMIT",
        "LISTENER_FAILED",
    }

    def __init__(
        self,
        *,
        api_key: str,
        base_url: str,
        settings_col,
        get_usd_inr,
        now_ist,
        default_markup_percent: float = 20.0,
    ):
        self.api_key = (api_key or "").strip()
        self.base_url = (base_url or "https://hearttgstoreapi.duckdns.org/api").rstrip("/")
        self.settings_col = settings_col
        self.get_usd_inr = get_usd_inr
        self.now_ist = now_ist
        self.default_markup_percent = float(default_markup_percent)
        self._p1_cache = {"ts": 0.0, "items": [], "balance": None}
        self._p2_cache = {"ts": 0.0, "items": [], "balance": None}
        self._p1_unavailable_until = {}
        self._markup_cache = (0.0, None)          # (timestamp, value) — 30 s
        self._p1_fail_until = 0.0                  # after a failed refresh: don't hammer the supplier
        self._p2_fail_until = 0.0
        self._locks = {}                           # single-flight refresh locks
        self._bg_tasks = {}                        # background refresh tasks
        self._warm_task = None                     # keeps both stock caches warm
        self._session = None                       # shared aiohttp.ClientSession
        self._session_lock = None                  # created lazily inside the running loop

    # ── persistent HTTP session (connection pooling) ───────────────────
    async def _get_session(self) -> aiohttp.ClientSession:
        """One shared ClientSession for every supplier call: TCP/TLS connections are
        reused instead of being re-negotiated per request. Re-created if closed."""
        session = self._session
        if session is not None and not session.closed:
            return session
        if self._session_lock is None:
            self._session_lock = asyncio.Lock()
        async with self._session_lock:
            if self._session is None or self._session.closed:
                connector = aiohttp.TCPConnector(
                    limit=100,
                    limit_per_host=30,
                    ttl_dns_cache=300,
                    keepalive_timeout=30,
                    enable_cleanup_closed=True,
                )
                self._session = aiohttp.ClientSession(connector=connector)
            return self._session

    async def close(self) -> None:
        """Safe to call more than once (and when no request was ever made)."""
        for task in [self._warm_task, *self._bg_tasks.values()]:
            if task is not None and not task.done():
                task.cancel()
        self._warm_task, self._bg_tasks = None, {}
        session, self._session = self._session, None
        if session is not None and not session.closed:
            try:
                await session.close()
            except Exception as exc:  # pragma: no cover - shutdown best effort
                logging.warning("%s session close failed: %s", type(self).__name__, exc)

    @property
    def configured(self) -> bool:
        return bool(self.api_key)

    @staticmethod
    def ok(data) -> bool:
        return isinstance(data, dict) and data.get("success") is True

    @staticmethod
    def code(data) -> str:
        if not isinstance(data, dict):
            return "UNKNOWN"
        return str(data.get("code") or "").strip().upper()

    async def _request(self, method: str, path: str, *, params=None, json_body=None, timeout=25):
        if not self.api_key:
            return {
                "success": False,
                "code": "NOT_CONFIGURED",
                "error": "Server 3 API key is not configured",
                "_http_status": 0,
            }

        headers = {
            "X-API-Key": self.api_key,
            "Accept": "application/json",
        }
        if json_body is not None:
            headers["Content-Type"] = "application/json"

        url = f"{self.base_url}{path}"
        try:
            session = await self._get_session()
            async with session.request(
                method.upper(),
                url,
                params=params,
                json=json_body,
                headers=headers,
                timeout=aiohttp.ClientTimeout(total=timeout),
            ) as response:
                try:
                    body = await response.json(content_type=None)
                except Exception:
                    body = {
                        "success": False,
                        "code": "BAD_RESPONSE",
                        "error": (await response.text())[:500],
                    }
                if not isinstance(body, dict):
                    body = {
                        "success": False,
                        "code": "BAD_RESPONSE",
                        "error": "Supplier returned a non-JSON object",
                        "raw": body,
                    }
                body.setdefault("success", response.status < 400)
                body["_http_status"] = response.status
                return body
        except asyncio.TimeoutError:
            return {
                "success": False,
                "code": "TIMEOUT",
                "error": "Supplier API timeout",
                "_http_status": 0,
            }
        except Exception as exc:
            logging.error("Server 3 API %s %s failed: %s", method, path, exc)
            return {
                "success": False,
                "code": "CONNECTION_ERROR",
                "error": "Supplier API connection error",
                "_http_status": 0,
            }

    async def get_markup_percent(self) -> float:
        ts, cached = self._markup_cache
        if cached is not None and time.time() - ts < 30:
            return cached
        setting = await self.settings_col.find_one({"key": "server3_markup_percent"})
        value = (
            float(setting.get("value", self.default_markup_percent))
            if setting is not None else self.default_markup_percent
        )
        self._markup_cache = (time.time(), value)
        return value

    async def set_markup_percent(self, value: float):
        await self.settings_col.update_one(
            {"key": "server3_markup_percent"},
            {"$set": {"value": float(value), "updated_at": self.now_ist()}},
            upsert=True,
        )
        self._markup_cache = (0.0, None)

    async def calculate_price_usd(self, supplier_price: float) -> dict:
        usd_inr = await self.get_usd_inr()
        wholesale_inr = round(float(supplier_price) * float(usd_inr), 2)
        markup_percent = await self.get_markup_percent()
        retail_inr = round(wholesale_inr * (1 + markup_percent / 100.0), 2)
        return {
            "supplier_price": float(supplier_price),
            "usd_inr": float(usd_inr),
            "wholesale_inr": wholesale_inr,
            "markup_percent": markup_percent,
            "retail_inr": retail_inr,
        }

    async def calculate_price_inr(self, base_inr: float) -> dict:
        wholesale_inr = round(float(base_inr), 2)
        markup_percent = await self.get_markup_percent()
        retail_inr = round(wholesale_inr * (1 + markup_percent / 100.0), 2)
        return {
            "wholesale_inr": wholesale_inr,
            "markup_percent": markup_percent,
            "retail_inr": retail_inr,
        }

    async def stock(self, provider: int):
        # 12 s is plenty for a stock list; a dead supplier must not hold a user for 25 s.
        return await self._request("GET", "/stock", params={"server": int(provider)}, timeout=12)

    # ── stock caches: instant answers, background refresh, one supplier call at a time ──
    P1_FRESH, P2_FRESH, MAX_STALE = 30, 60, 3600

    def _lock(self, name: str) -> asyncio.Lock:
        if name not in self._locks:
            self._locks[name] = asyncio.Lock()
        return self._locks[name]

    def _spawn(self, name: str, factory):
        """Fire-and-forget refresh; at most one per cache."""
        task = self._bg_tasks.get(name)
        if task is not None and not task.done():
            return

        async def _run():
            try:
                await factory()
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                logging.warning("Server 3 background refresh %s failed: %s", name, exc)

        self._bg_tasks[name] = asyncio.ensure_future(_run())

    def _visible_p1(self, items):
        now = time.time()
        out = []
        for row in items:
            key = str(row.get("key") or "")
            until = float(self._p1_unavailable_until.get(key, 0) or 0)
            if until > now:
                continue
            if until:
                self._p1_unavailable_until.pop(key, None)
            out.append(row)
        return out

    async def _refresh_provider1(self) -> bool:
        async with self._lock("p1"):
            if self._p1_cache["items"] and time.time() - self._p1_cache["ts"] < 5:
                return True                       # another caller refreshed a moment ago
            result = await self.stock(1)
            if not self.ok(result):
                self._p1_fail_until = time.time() + 10
                return False
            items = []
            for row in result.get("stock") or []:
                if not isinstance(row, dict):
                    continue
                # OTP bot: never expose supplier session-only categories.
                if str(row.get("type") or "").lower() != "account":
                    continue
                if int(row.get("quantity", 0) or 0) <= 0:
                    continue
                if not str(row.get("key") or "").strip():
                    continue
                items.append(dict(row))
            self._p1_cache = {"ts": time.time(), "items": items, "balance": result.get("balance")}
            self._p1_fail_until = 0.0
            return True

    async def _refresh_provider2(self) -> bool:
        async with self._lock("p2"):
            if self._p2_cache["items"] and time.time() - self._p2_cache["ts"] < 5:
                return True
            result = await self.stock(2)
            if not self.ok(result):
                self._p2_fail_until = time.time() + 10
                return False
            items = []
            for row in result.get("stock") or []:
                if not isinstance(row, dict):
                    continue
                code = str(row.get("country") or "").strip().upper()
                if not code:
                    key = str(row.get("key") or "")
                    if key.startswith("s2_"):
                        code = key[3:].upper()
                if not code:
                    continue
                item = dict(row)
                item["country"] = code
                items.append(item)
            self._p2_cache = {"ts": time.time(), "items": items, "balance": result.get("balance")}
            self._p2_fail_until = 0.0
            return True

    async def provider1_stock(self, force: bool = False):
        cache, now = self._p1_cache, time.time()
        age = now - cache["ts"]
        if not force and cache["items"]:
            if age < self.P1_FRESH:
                return self._visible_p1(cache["items"])
            if age < self.MAX_STALE:              # stale: answer instantly, refresh behind the scenes
                if now >= self._p1_fail_until:
                    self._spawn("p1", self._refresh_provider1)
                return self._visible_p1(cache["items"])
        if not force and now < self._p1_fail_until:
            return self._visible_p1(cache["items"])   # supplier just failed — don't make users wait again
        await self._refresh_provider1()
        return self._visible_p1(self._p1_cache["items"])

    async def provider2_countries(self, force: bool = False):
        cache, now = self._p2_cache, time.time()
        age = now - cache["ts"]
        if not force and cache["items"]:
            if age < self.P2_FRESH:
                return list(cache["items"])
            if age < self.MAX_STALE:
                if now >= self._p2_fail_until:
                    self._spawn("p2", self._refresh_provider2)
                return list(cache["items"])
        if not force and now < self._p2_fail_until:
            return list(cache["items"])
        await self._refresh_provider2()
        return list(self._p2_cache["items"])

    def start_warmer(self, interval: int = 20):
        """Keep both stock lists warm so a tap never has to wait for the supplier."""
        if self._warm_task is not None and not self._warm_task.done():
            return

        async def _loop():
            while True:
                try:
                    if self.configured:
                        await asyncio.gather(self._refresh_provider1(), self._refresh_provider2(),
                                             return_exceptions=True)
                except asyncio.CancelledError:
                    raise
                except Exception as exc:
                    logging.warning("Server 3 warmer error: %s", exc)
                await asyncio.sleep(interval)

        self._warm_task = asyncio.ensure_future(_loop())

    def mark_provider1_unavailable(self, item_key: str, ttl_seconds: int = 90):
        """Temporarily hide a Provider 1 row that failed the live deliverability check.
        (Only that row is hidden — the rest of the cached list stays instantly available.)"""
        key = str(item_key or "").strip()
        if not key:
            return
        self._p1_unavailable_until[key] = time.time() + max(15, int(ttl_seconds))

    async def provider1_preview(self, item_key: str):
        return await self._request(
            "POST",
            "/buy/account",
            json_body={"item_key": item_key, "delivery": "otp", "test_mode": True},
            timeout=35,
        )

    async def provider1_quote(self, item_key: str):
        return await self._request(
            "POST",
            "/buy/account",
            json_body={"item_key": item_key, "delivery": "otp"},
            timeout=35,
        )

    async def provider1_confirm(self, confirm_token: str):
        return await self._request(
            "POST",
            "/buy/account",
            json_body={"confirm_token": confirm_token},
            timeout=45,
        )

    async def provider2_preview(self, country: str, price=None):
        payload = {
            "country": str(country).upper(),
            "delivery": "otp",
            "test_mode": True,
        }
        if price is not None:
            payload["price"] = float(price)
        return await self._request("POST", "/buy/server2", json_body=payload, timeout=30)

    async def provider2_buy(self, country: str, price=None):
        payload = {
            "country": str(country).upper(),
            "delivery": "otp",
        }
        if price is not None:
            payload["price"] = float(price)
        return await self._request("POST", "/buy/server2", json_body=payload, timeout=50)

    async def request_otp(self, order_id: str):
        return await self._request(
            "POST",
            "/order/otp",
            json_body={"order_id": str(order_id)},
            timeout=20,
        )

    async def order_status(self, order_id: str):
        return await self._request(
            "GET",
            "/order/status",
            params={"order_id": str(order_id)},
            timeout=20,
        )

    async def order_session(self, order_id: str):
        # Admin/recovery utility only. Never called automatically in OTP flow.
        return await self._request(
            "GET",
            "/order/session",
            params={"order_id": str(order_id)},
            timeout=30,
        )
