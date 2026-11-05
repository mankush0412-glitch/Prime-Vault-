import asyncio
import time
import logging
import aiohttp


class VNHServer:
    """
    VNHAPI integration kept separate from the main Telegram bot.

    Handles:
      - API authentication / requests
      - API health check
      - available Telegram countries
      - live supplier country price
      - admin-configurable markup
      - number reservation
      - OTP/password retrieval
      - supplier-price -> INR conversion
    """

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
        self.base_url = (base_url or "https://api.vnhotp.com").rstrip("/")
        self.settings_col = settings_col
        self.get_usd_inr = get_usd_inr
        self.now_ist = now_ist
        self.default_markup_percent = float(default_markup_percent)
        self._country_cache = {"ts": 0.0, "items": []}
        self._markup_cache = (0.0, None)          # (timestamp, value) — 30 s
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
        if isinstance(data, list):
            return len(data) > 0 and data[0] is True
        if not isinstance(data, dict):
            return False
        if data.get("success") is True:
            return True
        return str(data.get("status", "")).lower() == "success"

    async def _get(self, path: str, **params):
        if not self.api_key:
            return {"success": False, "message": "VNH API key is not configured"}

        query = {"api_key": self.api_key}
        query.update(params)

        try:
            session = await self._get_session()
            async with session.get(
                f"{self.base_url}{path}",
                params=query,
                headers={"Accept": "application/json"},
                timeout=aiohttp.ClientTimeout(total=20),
            ) as response:
                try:
                    body = await response.json(content_type=None)
                except Exception:
                    body = {
                        "success": False,
                        "message": (await response.text())[:500],
                    }

                if response.status >= 400 and isinstance(body, dict):
                    body.setdefault("success", False)
                return body

        except asyncio.TimeoutError:
            return {"success": False, "message": "VNH supplier API timeout"}
        except Exception as exc:
            logging.error("VNHAPI request error %s: %s", path, exc)
            return {"success": False, "message": "VNH supplier API connection error"}

    async def get_markup_percent(self) -> float:
        ts, cached = self._markup_cache
        if cached is not None and time.time() - ts < 30:
            return cached
        setting = await self.settings_col.find_one({"key": "vnh_markup_percent"})
        value = (
            float(setting.get("value", self.default_markup_percent))
            if setting is not None else self.default_markup_percent
        )
        self._markup_cache = (time.time(), value)
        return value

    async def set_markup_percent(self, value: float):
        value = float(value)
        await self.settings_col.update_one(
            {"key": "vnh_markup_percent"},
            {"$set": {"value": value, "updated_at": self.now_ist()}},
            upsert=True,
        )
        self._markup_cache = (0.0, None)

    async def check(self):
        return await self._get("/check")

    async def available_countries(self, force: bool = False):
        now = time.time()
        if (
            not force
            and self._country_cache["items"]
            and now - self._country_cache["ts"] < 60
        ):
            return self._country_cache["items"]

        result = await self._get("/tg/available_countries")

        # VNH currently returns:
        # [true, {"BD": {...}, "IN": {...}, ...}]
        # Keep compatibility with dict-style responses too.
        raw = None

        if isinstance(result, list):
            if len(result) >= 2 and result[0] is True:
                raw = result[1]
            else:
                return []

        elif isinstance(result, dict):
            if not self.ok(result):
                return []
            raw = result.get("data", result)

        else:
            return []

        countries = []

        # Current VNH format: dict keyed by country code
        if isinstance(raw, dict):
            # Sometimes APIs may nest it under "countries".
            if "countries" in raw and isinstance(raw["countries"], (dict, list)):
                raw = raw["countries"]

            if isinstance(raw, dict):
                for key, item in raw.items():
                    if not isinstance(item, dict):
                        continue

                    code = str(
                        item.get("code")
                        or item.get("country_code")
                        or key
                        or ""
                    ).strip().upper()

                    name = str(
                        item.get("name")
                        or item.get("country")
                        or code
                    ).strip()

                    qty = item.get("qty", 0)
                    price = item.get("price")

                    if code:
                        countries.append({
                            "code": code,
                            "name": name or code,
                            "qty": qty,
                            "price": price,
                            "code_num": item.get("code_Num"),
                        })

        # Compatibility with list-style country payloads
        elif isinstance(raw, list):
            for item in raw:
                if isinstance(item, str):
                    code = item.strip().upper()
                    if code:
                        countries.append({
                            "code": code,
                            "name": code,
                            "qty": 0,
                            "price": None,
                            "code_num": None,
                        })
                    continue

                if not isinstance(item, dict):
                    continue

                code = str(
                    item.get("country_code")
                    or item.get("code")
                    or item.get("iso")
                    or ""
                ).strip().upper()

                name = str(
                    item.get("country")
                    or item.get("name")
                    or code
                ).strip()

                if code:
                    countries.append({
                        "code": code,
                        "name": name or code,
                        "qty": item.get("qty", 0),
                        "price": item.get("price"),
                        "code_num": item.get("code_Num"),
                    })

        self._country_cache = {"ts": now, "items": countries}
        return countries

    async def country_info(self, code: str):
        return await self._get("/tg/country_info", code=code.upper())

    async def place_order(self, code: str):
        return await self._get("/tg/place_order", code=code.upper())

    async def get_code(self, number: str):
        return await self._get("/tg/get_code", number=number)

    async def supplier_price_to_inr(self, supplier_price: float) -> float:
        usd_inr = await self.get_usd_inr()
        return round(float(supplier_price) * float(usd_inr), 2)

    async def calculate_price(self, supplier_price: float) -> dict:
        wholesale_inr = await self.supplier_price_to_inr(supplier_price)
        markup_percent = await self.get_markup_percent()
        retail_inr = round(
            wholesale_inr * (1 + markup_percent / 100.0),
            2,
        )
        return {
            "supplier_price": float(supplier_price),
            "wholesale_inr": wholesale_inr,
            "markup_percent": markup_percent,
            "retail_inr": retail_inr,
        }

    async def get_country_live_price(self, code: str):
        result = await self.country_info(code)
        if not self.ok(result):
            return {
                "success": False,
                "message": result.get("message", "Could not fetch live supplier price")
                if isinstance(result, dict)
                else "Could not fetch live supplier price",
            }

        data = result.get("data") or {}
        try:
            supplier_price = float(data.get("price"))
        except Exception:
            return {"success": False, "message": "Supplier returned an invalid price"}

        pricing = await self.calculate_price(supplier_price)
        return {
            "success": True,
            "data": data,
            **pricing,
        }
