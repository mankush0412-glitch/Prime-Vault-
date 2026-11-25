"""
╔══════════════════════════════════════════════════╗
║          NEXT LEVEL VAULT BOT                    ║
║   Telegram Account (OTP) Seller Bot              ║
║   Final – Fast + Razorpay + Self-Ping           ║
║   Run:  python bot.py                           ║
╚══════════════════════════════════════════════════╝
"""

import os
import io
import unicodedata
import re
import uuid
import asyncio
import contextlib
import zipfile
import tempfile
import hashlib
import logging
import hmac
import json
from datetime import datetime, timedelta
from typing import Optional, List, Dict, Any

from dotenv import load_dotenv
from motor.motor_asyncio import AsyncIOMotorClient
from bson import ObjectId
from bson import ObjectId as _ObjId
from telethon import TelegramClient, events, Button, functions, types
from telethon.sessions import StringSession
from telethon.errors import (
    UserNotParticipantError,
    ChatAdminRequiredError,
    ChannelPrivateError,
    FloodWaitError,
)
from account_manager import AccountManager
from vnh_server import VNHServer
from ui_style import StyledMarkdown, RAW, strip_emoji, resolve_style, STYLE_RED, STYLE_BLUE, STYLE_GREEN, PLAIN
import aiohttp
import time
import html as _html
import secrets
import signal
import shutil
import random
from decimal import Decimal
from urllib.parse import quote as _urlquote
from pymongo.errors import DuplicateKeyError
from telethon.errors import SessionPasswordNeededError, MessageNotModifiedError
from telethon.sessions import SQLiteSession
from account_manager import ACCESS_VALIDITY
from server3_server import Server3Server
from razorpay_api_verification import (
    expected_paise, captured_payment, qr_payment_ids, link_payment_ids,
)

# ─── 1. ENV & CONFIG ────────────────────────────────────────────
load_dotenv()

API_ID    = int(os.getenv("API_ID", "0"))
API_HASH  = os.getenv("API_HASH", "")
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
MONGO_URL = os.getenv("MONGO_URL", "mongodb://localhost:27017")
OWNER_ID  = int(os.getenv("OWNER_ID", "0"))
DB_NAME   = os.getenv("DB_NAME", "stark_bot")
RAZORPAY_KEY_ID = os.getenv("RAZORPAY_KEY_ID", "")
RAZORPAY_KEY_SECRET = os.getenv("RAZORPAY_KEY_SECRET", "")
RAZORPAY_WEBHOOK_SECRET = os.getenv("RAZORPAY_WEBHOOK_SECRET", "")
RAZORPAY_API_BASE = "https://api.razorpay.com/v1"
LOGS_CHANNEL_ID = int(os.getenv("LOGS_CHANNEL_ID", "0") or "0")
RENDER_EXTERNAL_URL = os.getenv("PUBLIC_URL", "") or os.getenv("RENDER_EXTERNAL_URL", "")  # works the same on Render, AWS, or any host — just set PUBLIC_URL to wherever this is reachable
VNH_API_KEY  = os.getenv("VNH_API_KEY", "")
VNH_API_BASE = os.getenv("VNH_API_BASE", "https://api.vnhotp.com")
VNH_MARKUP_PERCENT = float(os.getenv("VNH_MARKUP_PERCENT", "20"))

# ── Server 3 (Heart TG Store API — Provider 1 / Provider 2) ──
SERVER3_API_KEY        = os.getenv("SERVER3_API_KEY", "").strip()
SERVER3_API_BASE       = os.getenv("SERVER3_API_BASE", "https://hearttgstoreapi.duckdns.org/api").strip()
SERVER3_MARKUP_PERCENT = float(os.getenv("SERVER3_MARKUP_PERCENT", "20") or "20")

# ── Bulk buy / session ZIP delivery ──
BULK_BUY_MAX_QTY = max(2, int(os.getenv("BULK_BUY_MAX_QTY", "20") or "20"))
SESSION_READER_BOT_USERNAME = os.getenv("SESSION_READER_BOT_USERNAME", "").strip()

# ── Referral (join reward is editable live from the admin panel) ──
REFERRAL_SIGNUP_BONUS  = float(os.getenv("REFERRAL_SIGNUP_BONUS", "0.05") or "0.05")
REFERRAL_BONUS_PERCENT = float(os.getenv("REFERRAL_BONUS_PERCENT", "10") or "10")
REFERRAL_BONUS_MAX     = float(os.getenv("REFERRAL_BONUS_MAX", "5") or "5")

def _env_chat_id(name: str, fallback: int = 0) -> int:
    raw = os.getenv(name, "").strip()
    if not raw:
        return fallback
    try:
        return int(raw)
    except ValueError:
        logging.warning(f"{name} is not a valid integer — ignored.")
        return fallback

# ── Channels: private logs / public purchase feed / stock announcements / payment review ──
PUBLIC_LOG_CHANNEL_ID   = _env_chat_id("PUBLIC_LOG_CHANNEL_ID")
ANNOUNCEMENT_CHANNEL_ID = _env_chat_id("ANNOUNCEMENT_CHANNEL_ID", PUBLIC_LOG_CHANNEL_ID)
PAYMENT_GROUP_ID        = _env_chat_id("PAYMENT_GROUP_ID", LOGS_CHANNEL_ID)

# ── Razorpay without a webhook (API polling) ──
RAZORPAY_ENABLE_WEBHOOK   = os.getenv("RAZORPAY_ENABLE_WEBHOOK", "true").strip().lower() in ("1", "true", "yes")
RAZORPAY_API_POLL_SECONDS = max(30, int(os.getenv("RAZORPAY_API_POLL_SECONDS", "60") or "60"))
RAZORPAY_QR_EXPIRY_SECONDS = int(os.getenv("RAZORPAY_QR_EXPIRY_SECONDS", "900") or "900")

ADMIN_IDS: List[int] = [OWNER_ID] if OWNER_ID else []
for _a in os.getenv("ADMIN_IDS", "").split(","):
    try:
        _id = int(_a.strip())
        if _id not in ADMIN_IDS:
            ADMIN_IDS.append(_id)
    except ValueError:
        pass

_fj_raw = os.getenv("FORCE_JOIN_CHAT_IDS", os.getenv("FORCE_JOIN_CHAT_ID", "")).strip()
RAW_CHAT_IDS: List[str] = [x.strip() for x in _fj_raw.split(",") if x.strip()]

if not all([API_ID, API_HASH, BOT_TOKEN, OWNER_ID]):
    raise ValueError("❌ .env incomplete!  set API_ID, API_HASH, BOT_TOKEN, OWNER_ID.")

# ─── 2. LOGGING ──────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("NextLevelVault")

# ─── 3. MONGODB ──────────────────────────────────────────────────
_mongo_client    = AsyncIOMotorClient(MONGO_URL)
db               = _mongo_client[DB_NAME]
accounts_col     = db["accounts"]
users_col        = db["users"]
orders_col       = db["orders"]
deposits_col     = db["deposits"]
settings_col     = db["settings"]
countries_col    = db["countries"]
cat_prices_col   = db["category_prices"]     # price of a country INSIDE one category: {code, category, price}
bot_admins_col   = db["bot_admins"]
categories_col   = db["categories"]
packages_col     = db["packages"]
bulk_orders_col  = db["bulk_orders"]
referral_signup_claims_col = db["referral_signup_claims"]
stock_deeplinks_col        = db["stock_deeplinks"]

# ─── 4. BOT INSTANCE ────────────────────────────────────────────
_session_name = "next_level_vault_" + hashlib.md5(BOT_TOKEN.encode()).hexdigest()[:8]
bot = TelegramClient(_session_name, API_ID, API_HASH)
bot.parse_mode = StyledMarkdown   # markdown + real blockquotes + auto heading style (see ui_style.py)

pending_otp_requests: Dict = {}
user_states: Dict           = {}
acc_mgr: Optional[AccountManager] = None

# ─── 4b. VNH SUPPLIER API (Server 2) ────────────────────────────
def now_ist():
    return datetime.utcnow() + timedelta(hours=5, minutes=30)

_usd_inr: float = 90.0
_usd_fetched: float = 0

_usd_lock = None
async def get_usd_inr() -> float:
    global _usd_inr, _usd_fetched, _usd_lock
    if time.time() - _usd_fetched < 3600:
        return _usd_inr
    if _usd_lock is None:
        _usd_lock = asyncio.Lock()
    async with _usd_lock:
        if time.time() - _usd_fetched < 3600:      # someone else refreshed while we waited
            return _usd_inr
        try:
            async with aiohttp.ClientSession() as s_:
                async with s_.get("https://open.er-api.com/v6/latest/USD",
                                  timeout=aiohttp.ClientTimeout(total=4)) as r:
                    d = await r.json(content_type=None)
                    if d.get("result") == "success":
                        _usd_inr = float(d["rates"]["INR"])
                        _usd_fetched = time.time()
                        return _usd_inr
            raise RuntimeError("bad rate response")
        except Exception as e:
            logging.warning(f"USD/INR fetch failed, using {_usd_inr}: {e}")
            _usd_fetched = time.time() - 3600 + 300     # do not retry for 5 minutes
    return _usd_inr

vnh_server = VNHServer(
    api_key=VNH_API_KEY,
    base_url=VNH_API_BASE,
    settings_col=settings_col,
    get_usd_inr=get_usd_inr,
    now_ist=now_ist,
    default_markup_percent=VNH_MARKUP_PERCENT,
)

# ─── 5. DEFAULT DATA ────────────────────────────────────────────
DEFAULT_SETTINGS = {
    "bot_name":            "Prime Vault",
    "upi_id":              "",
    "upi_name":            "Prime Vault",
    "support_link":        "",
    "referral_bonus":      0,
    "referral_percent":    0,
    "min_deposit":         10.0,
    "welcome_photo":       "",
    "whatsapp_enabled":    False,
    "auto_verify_delay":   10,
    "payment_webhook_url": "",
    "default_2fa":         "",
    "server_count":        2,
    "vnh_server_number":   2,
    "logs_channel_id":     0,
    "terms_text":          "",
    "sales_link":          "",
    "max_deposit":         100000,
}

DEFAULT_CATEGORIES = [
    {"name": "Fresh Accounts", "icon": "🆕", "order": 1},
    {"name": "Cheap Accounts", "icon": "💰", "order": 2},
    {"name": "Old Accounts",   "icon": "📅", "order": 3},
    {"name": "Spam Accounts",  "icon": "📧", "order": 4},
    {"name": "Rare Accounts",  "icon": "⭐", "order": 5},
    {"name": "Number Change",  "icon": "🔄", "order": 6},
]

DEFAULT_PACKAGES = [
    {"credits": 10, "price": 10.0, "usdt": 0.11, "stars": 10},
    {"credits": 25, "price": 25.0, "usdt": 0.27, "stars": 25},
    {"credits": 50, "price": 50.0, "usdt": 0.55, "stars": 50},
    {"credits": 100, "price": 100.0, "usdt": 1.10, "stars": 100},
]

DEFAULT_COUNTRIES = [
    {"code": "IN", "name": "India",       "flag": "🇮🇳", "price": 30.0},
    {"code": "BD", "name": "Bangladesh",  "flag": "🇧🇩", "price": 28.0},
    {"code": "PK", "name": "Pakistan",    "flag": "🇵🇰", "price": 25.0},
    {"code": "NG", "name": "Nigeria",     "flag": "🇳🇬", "price": 20.0},
    {"code": "ID", "name": "Indonesia",   "flag": "🇮🇩", "price": 28.0},
    {"code": "US", "name": "USA",         "flag": "🇺🇸", "price": 50.0},
    {"code": "VN", "name": "Vietnam",     "flag": "🇻🇳", "price": 22.0},
    {"code": "MM", "name": "Myanmar",     "flag": "🇲🇲", "price": 20.0},
    {"code": "KE", "name": "Kenya",       "flag": "🇰🇪", "price": 22.0},
    {"code": "CO", "name": "Colombia",    "flag": "🇨🇴", "price": 25.0},
    {"code": "ZW", "name": "Zimbabwe",    "flag": "🇿🇼", "price": 18.0},
    {"code": "GB", "name": "UK",          "flag": "🇬🇧", "price": 45.0},
    {"code": "RU", "name": "Russia",      "flag": "🇷🇺", "price": 30.0},
    {"code": "BR", "name": "Brazil",      "flag": "🇧🇷", "price": 25.0},
    {"code": "PH", "name": "Philippines", "flag": "🇵🇭", "price": 22.0},
    {"code": "EG", "name": "Egypt",       "flag": "🇪🇬", "price": 20.0},
]

ISO = """AF:Afghanistan;AL:Albania;DZ:Algeria;AS:American Samoa;AD:Andorra;AO:Angola;AI:Anguilla;AG:Antigua and Barbuda;AR:Argentina;AM:Armenia;AW:Aruba;AU:Australia;AT:Austria;AZ:Azerbaijan;BS:Bahamas;BH:Bahrain;BD:Bangladesh;BB:Barbados;BY:Belarus;BE:Belgium;BZ:Belize;BJ:Benin;BM:Bermuda;BT:Bhutan;BO:Bolivia;BA:Bosnia and Herzegovina;BW:Botswana;BR:Brazil;BN:Brunei;BG:Bulgaria;BF:Burkina Faso;BI:Burundi;KH:Cambodia;CM:Cameroon;CA:Canada;CV:Cape Verde;KY:Cayman Islands;CF:Central African Republic;TD:Chad;CL:Chile;CN:China;CO:Colombia;KM:Comoros;CG:Congo;CD:DR Congo;CR:Costa Rica;CI:Ivory Coast;HR:Croatia;CU:Cuba;CY:Cyprus;CZ:Czech Republic;DK:Denmark;DJ:Djibouti;DM:Dominica;DO:Dominican Republic;EC:Ecuador;EG:Egypt;SV:El Salvador;GQ:Equatorial Guinea;ER:Eritrea;EE:Estonia;SZ:Eswatini;ET:Ethiopia;FJ:Fiji;FI:Finland;FR:France;GF:French Guiana;PF:French Polynesia;GA:Gabon;GM:Gambia;GE:Georgia;DE:Germany;GH:Ghana;GI:Gibraltar;GR:Greece;GL:Greenland;GD:Grenada;GP:Guadeloupe;GU:Guam;GT:Guatemala;GN:Guinea;GW:Guinea-Bissau;GY:Guyana;HT:Haiti;HN:Honduras;HK:Hong Kong;HU:Hungary;IS:Iceland;IN:India;ID:Indonesia;IR:Iran;IQ:Iraq;IE:Ireland;IL:Israel;IT:Italy;JM:Jamaica;JP:Japan;JO:Jordan;KZ:Kazakhstan;KE:Kenya;KI:Kiribati;KP:North Korea;KR:South Korea;KW:Kuwait;KG:Kyrgyzstan;LA:Laos;LV:Latvia;LB:Lebanon;LS:Lesotho;LR:Liberia;LY:Libya;LI:Liechtenstein;LT:Lithuania;LU:Luxembourg;MO:Macau;MG:Madagascar;MW:Malawi;MY:Malaysia;MV:Maldives;ML:Mali;MT:Malta;MQ:Martinique;MR:Mauritania;MU:Mauritius;MX:Mexico;FM:Micronesia;MD:Moldova;MC:Monaco;MN:Mongolia;ME:Montenegro;MA:Morocco;MZ:Mozambique;MM:Myanmar;NA:Namibia;NR:Nauru;NP:Nepal;NL:Netherlands;NC:New Caledonia;NZ:New Zealand;NI:Nicaragua;NE:Niger;NG:Nigeria;MK:North Macedonia;NO:Norway;OM:Oman;PK:Pakistan;PW:Palau;PS:Palestine;PA:Panama;PG:Papua New Guinea;PY:Paraguay;PE:Peru;PH:Philippines;PL:Poland;PT:Portugal;PR:Puerto Rico;QA:Qatar;RE:Reunion;RO:Romania;RU:Russia;RW:Rwanda;KN:Saint Kitts and Nevis;LC:Saint Lucia;VC:Saint Vincent;WS:Samoa;SM:San Marino;ST:Sao Tome and Principe;SA:Saudi Arabia;SN:Senegal;RS:Serbia;SC:Seychelles;SL:Sierra Leone;SG:Singapore;SK:Slovakia;SI:Slovenia;SB:Solomon Islands;SO:Somalia;ZA:South Africa;SS:South Sudan;ES:Spain;LK:Sri Lanka;SD:Sudan;SR:Suriname;SE:Sweden;CH:Switzerland;SY:Syria;TW:Taiwan;TJ:Tajikistan;TZ:Tanzania;TH:Thailand;TL:Timor-Leste;TG:Togo;TO:Tonga;TT:Trinidad and Tobago;TN:Tunisia;TR:Turkey;TM:Turkmenistan;UG:Uganda;UA:Ukraine;AE:UAE;GB:UK;US:USA;UY:Uruguay;UZ:Uzbekistan;VU:Vanuatu;VA:Vatican City;VE:Venezuela;VN:Vietnam;VG:British Virgin Islands;VI:US Virgin Islands;YE:Yemen;ZM:Zambia;ZW:Zimbabwe;XK:Kosovo"""
ALIASES = {"united states":"US","united states of america":"US","america":"US","usa":"US","uk":"GB","united kingdom":"GB","britain":"GB","great britain":"GB","england":"GB","uae":"AE","united arab emirates":"AE","emirates":"AE","russian federation":"RU","korea":"KR","republic of korea":"KR","czechia":"CZ","cote divoire":"CI","ivory coast":"CI","turkiye":"TR","burma":"MM","viet nam":"VN","swaziland":"SZ","macedonia":"MK","east timor":"TL","congo kinshasa":"CD","democratic republic of the congo":"CD","drc":"CD","holland":"NL","cabo verde":"CV","saint vincent and the grenadines":"VC"}

_ISO_NAMES: Dict[str, str] = dict(x.split(":", 1) for x in ISO.split(";"))
_ISO_BY_NAME: Dict[str, str] = {re.sub(r"[^a-z ]", "", n.lower()): c for c, n in _ISO_NAMES.items()}
_ISO_BY_NAME.update(ALIASES)

def _flag_for(code: str) -> str:
    code = (code or "").upper()
    if len(code) == 2 and code.isalpha():
        return "".join(chr(0x1F1E6 + ord(ch) - 65) for ch in code)
    return "🌍"

def resolve_country(text: str) -> dict:
    """'Turkey' / 'tr' / 'united states' -> {code, name, flag}.  Unknown -> {suggest: [...]}"""
    import difflib
    t = re.sub(r"[^a-z ]", "", (text or "").lower()).strip()
    if not t:
        return {"suggest": []}
    raw = (text or "").strip()
    if len(raw) == 2 and raw.upper() in _ISO_NAMES:
        c = raw.upper()
    elif t in _ISO_BY_NAME:
        c = _ISO_BY_NAME[t]
    else:
        close = difflib.get_close_matches(t, list(_ISO_BY_NAME.keys()), n=3, cutoff=0.78)
        if len(close) == 1 or (close and difflib.SequenceMatcher(None, t, close[0]).ratio() > 0.9):
            c = _ISO_BY_NAME[close[0]]
        else:
            return {"suggest": [_ISO_NAMES[_ISO_BY_NAME[x]] for x in close]}
    return {"code": c, "name": _ISO_NAMES[c], "flag": COUNTRY_FLAGS.get(c) or _flag_for(c)}

async def _ensure_country(r: dict) -> dict:
    """Return the country doc for r; create it only if it does not exist yet (never asks twice)."""
    doc = await countries_col.find_one({"code": r["code"]})
    if doc:
        if not doc.get("is_active", True):
            await countries_col.update_one({"code": r["code"]}, {"$set": {"is_active": True}})
        return doc
    doc = {"code": r["code"], "name": r["name"], "flag": r["flag"], "price": 0.0, "is_active": True}
    await countries_col.insert_one(dict(doc))
    return doc

COUNTRY_FLAGS: Dict[str, str] = {c["code"]: c["flag"] for c in DEFAULT_COUNTRIES}
COUNTRY_FLAGS.update({
    "AU": "🇦🇺", "CA": "🇨🇦", "TR": "🇹🇷", "DE": "🇩🇪", "FR": "🇫🇷",
    "IT": "🇮🇹", "ES": "🇪🇸", "MX": "🇲🇽", "AR": "🇦🇷", "TH": "🇹🇭",
    "UA": "🇺🇦", "SA": "🇸🇦", "AE": "🇦🇪", "JP": "🇯🇵", "KR": "🇰🇷",
    "CN": "🇨🇳", "IR": "🇮🇷", "IQ": "🇮🇶", "MA": "🇲🇦", "UZ": "🇺🇿",
    "KZ": "🇰🇿", "NP": "🇳🇵", "LK": "🇱🇰", "SG": "🇸🇬", "MY": "🇲🇾",
})

# ─── 6. DATABASE INIT ────────────────────────────────────────────
async def init_db():
    await users_col.create_index("user_id", unique=True)
    await accounts_col.create_index([("country_code", 1), ("status", 1)])
    await accounts_col.create_index([("status", 1), ("category", 1), ("server", 1), ("country_code", 1)])
    await cat_prices_col.create_index([("code", 1), ("category", 1)], unique=True)
    await deposits_col.create_index("user_id")
    await orders_col.create_index("user_id")
    await settings_col.create_index("key", unique=True)
    await countries_col.create_index("code", unique=True)
    await bot_admins_col.create_index("telegram_id", unique=True)
    await categories_col.create_index("name", unique=True)
    await packages_col.create_index("credits", unique=True)

    for key, val in DEFAULT_SETTINGS.items():
        if not await settings_col.find_one({"key": key}):
            await settings_col.insert_one({"key": key, "value": val})

    for c in DEFAULT_COUNTRIES:
        if not await countries_col.find_one({"code": c["code"]}):
            await countries_col.insert_one({**c, "is_active": True})

    for cat in DEFAULT_CATEGORIES:
        if not await categories_col.find_one({"name": cat["name"]}):
            await categories_col.insert_one({**cat, "is_active": True})

    for pkg in DEFAULT_PACKAGES:
        if not await packages_col.find_one({"credits": pkg["credits"]}):
            await packages_col.insert_one(pkg)

    log.info("✅ Database initialised")

# ─── 7. SETTINGS CACHE ──────────────────────────────────────────
_settings_cache: Dict   = {}
_cache_ts: Optional[datetime] = None
_CACHE_TTL = 60

async def get_setting(key: str, default=None):
    global _settings_cache, _cache_ts
    now = datetime.utcnow()
    if _cache_ts is None or (now - _cache_ts).total_seconds() > _CACHE_TTL:
        _settings_cache = {}
        async for doc in settings_col.find({}):
            _settings_cache[doc["key"]] = doc["value"]
        _cache_ts = now
    return _settings_cache.get(key, default)

async def set_setting(key: str, value):
    global _settings_cache, _cache_ts
    await settings_col.update_one(
        {"key": key},
        {"$set": {"key": key, "value": value, "updated_at": datetime.utcnow()}},
        upsert=True,
    )
    _settings_cache = {}
    _cache_ts = None

# ─── 8. ADMIN HELPERS ────────────────────────────────────────────
async def get_all_admin_ids() -> List[int]:
    ids = list(ADMIN_IDS)
    async for a in bot_admins_col.find({"is_active": True}):
        if a["telegram_id"] not in ids:
            ids.append(a["telegram_id"])
    return ids

async def is_admin(user_id: int) -> bool:
    if user_id in ADMIN_IDS:
        return True
    doc = await bot_admins_col.find_one({"telegram_id": user_id, "is_active": True})
    return doc is not None

# ─── 9. BOT USERNAME CACHE ──────────────────────────────────────
_bot_username: Optional[str] = None
async def get_bot_username() -> str:
    global _bot_username
    if not _bot_username:
        me = await bot.get_me()
        _bot_username = me.username
    return _bot_username or ""

# ─── 10. FORCE‑JOIN ─────────────────────────────────────────────
def _parse_chat_id(raw: str):
    raw = raw.strip()
    if raw.startswith("@"):
        return raw
    try:
        return int(raw)
    except ValueError:
        return None

_chat_ent_cache: dict = {}
_invite_cache: dict = {}
_missing_cache: Dict[int, tuple] = {}

async def _get_chat_entity(parsed):
    ent = _chat_ent_cache.get(parsed)
    if ent is None:
        ent = await bot.get_entity(parsed)
        _chat_ent_cache[parsed] = ent
    return ent

async def _is_member_of(chat_raw: str, user_id: int) -> bool:
    parsed = _parse_chat_id(chat_raw)
    if parsed is None:
        return False
    try:
        entity = await _get_chat_entity(parsed)
        await bot.get_permissions(entity, user_id)
        return True
    except UserNotParticipantError:
        return False
    except (ChatAdminRequiredError, ChannelPrivateError):
        return True
    except Exception:
        return False

_member_ok: Dict[int, float] = {}
async def is_user_member(user_id: int) -> bool:
    if user_id in await _fj_exempt():
        return True                                          # approved by an admin — no force join
    chats = await get_force_join_chats()
    if not chats:
        return True
    if time.time() - _member_ok.get(user_id, 0) < 120:      # verified in the last 2 min
        return True
    results = await asyncio.gather(*[_is_member_of(raw, user_id) for raw in chats])   # all channels at once
    missing = [raw for raw, ok in zip(chats, results) if not ok]
    if missing:
        _member_ok.pop(user_id, None)
        _missing_cache[user_id] = (time.time(), missing)
        return False
    _member_ok[user_id] = time.time()
    _missing_cache.pop(user_id, None)
    if len(_member_ok) > 5000:
        _member_ok.clear()
    return True

_fj_exempt_cache: Optional[set] = None

async def _fj_exempt() -> set:
    """User IDs approved by an admin to use the bot without joining the force-join channels."""
    global _fj_exempt_cache
    if _fj_exempt_cache is None:
        raw = await get_setting("fj_exempt", []) or []
        _fj_exempt_cache = {int(x) for x in raw if str(x).lstrip("-").isdigit()}
    return _fj_exempt_cache

async def _fj_exempt_save(ids: set) -> None:
    global _fj_exempt_cache
    _fj_exempt_cache = {int(x) for x in ids}
    await set_setting("fj_exempt", sorted(_fj_exempt_cache))

async def _chan_title(raw: str) -> str:
    """Channel name as plain text (fancy unicode fonts in the title are normalised)."""
    t = raw
    try:
        ent = await _get_chat_entity(_parse_chat_id(raw))
        t = getattr(ent, "title", None) or raw
    except Exception:
        pass
    return unicodedata.normalize("NFKC", str(t)).strip() or str(raw)

async def _join_button(raw: str):
    title = await _chan_title(raw)
    if raw.startswith("@"):
        return [url_btn(f"Join {title}", f"https://t.me/{raw[1:]}", "primary")]
    link = _invite_cache.get(raw)
    if not link:
        try:
            entity = await _get_chat_entity(_parse_chat_id(raw))
            res = await bot(functions.messages.ExportChatInviteRequest(
                peer=entity, expire_date=None, usage_limit=0))
            link = res.link
            _invite_cache[raw] = link
        except Exception:
            link = None
    return [url_btn(f"Join {title}", link, "primary")] if link else None

async def send_join_message(event):
    uid = event.sender_id
    chats = await get_force_join_chats()
    cached = _missing_cache.get(uid)
    if cached and time.time() - cached[0] < 10:
        missing = cached[1]                       # just computed by is_user_member — no second round of checks
    else:
        res = await asyncio.gather(*[_is_member_of(raw, uid) for raw in chats])
        missing = [raw for raw, ok in zip(chats, res) if not ok]
    rows, titles = await asyncio.gather(
        asyncio.gather(*[_join_button(raw) for raw in missing]),
        asyncio.gather(*[_chan_title(raw) for raw in chats]))
    buttons = [r for r in rows if r]
    if not buttons:
        return
    lines = [f"{'❌' if raw in missing else '✅'} **{t}**" for raw, t in zip(chats, titles)]
    buttons.append([color_btn("Check Again", "check_join", "success")])
    await event.respond(
        fancy("⚠️ **You must join the channel(s) below to use this bot.**\n\n" + "\n".join(lines)),
        buttons=buttons,
    )

# ─── 11. USER HELPER ────────────────────────────────────────────
async def get_or_create_user(user_id: int,
                              referrer_id: Optional[int] = None) -> dict:
    user = await users_col.find_one({"user_id": user_id})
    if not user:
        import random, string
        ref_code = "".join(random.choices(string.ascii_uppercase + string.digits, k=8))
        user = {
            "user_id":           user_id,
            "balance":           0.0,
            "withdrawable":      0.0,
            "referral_code":     ref_code,
            "referred_by":       referrer_id,
            "referral_earnings": 0.0,
            "is_banned":         False,
            "joined_at":         datetime.utcnow(),
            "language":          "en",
            "tier":              "⭐",
        }
        await users_col.insert_one(user)
        await log_event(f"🆕 **New User**\n• User: `{user_id}`" + (f"\n• Referred by: `{referrer_id}`" if referrer_id else ""))
    return user

# ─── 12. COUNTRIES ──────────────────────────────────────────────
_cp_cache: Dict[tuple, float] = {}

async def get_cat_price(code: str, category, default=None):
    """Price of `code` inside `category` (fast: in-memory cache). Falls back to `default`."""
    if not category:
        return default
    key = (code, category)
    v = _cp_cache.get(key)
    if v is not None:
        return v
    doc = await cat_prices_col.find_one({"code": code, "category": category})
    if doc and doc.get("price") is not None:
        _cp_cache[key] = float(doc["price"])
        return _cp_cache[key]
    return default

async def set_cat_price(code: str, category: str, price: float):
    await cat_prices_col.update_one({"code": code, "category": category},
                                    {"$set": {"price": float(price)}}, upsert=True)
    _cp_cache[(code, category)] = float(price)

async def _migrate_cat_prices():
    """So a price can never leak from one category to another: freeze the current price per (country, category)."""
    try:
        async for g in accounts_col.aggregate([{"$group": {"_id": {"c": "$country_code", "k": "$category"}}}]):
            code, cat = (g.get("_id") or {}).get("c"), (g.get("_id") or {}).get("k")
            if not code or not cat:
                continue
            if await cat_prices_col.find_one({"code": code, "category": cat}, {"_id": 1}):
                continue
            c = await countries_col.find_one({"code": code}, {"price": 1})
            if c and c.get("price") is not None:
                await set_cat_price(code, cat, float(c["price"]))
    except Exception as e:
        log.warning(f"[migrate_cat_prices] {e}")

_ac_cache: Dict[tuple, tuple] = {}

async def get_active_countries(category: str = None, server: int = 1, year: str = None) -> List[dict]:
    """One grouped query (not one query per country) + a 3-second cache for paging / sorting."""
    key = (category, server, year)
    hit = _ac_cache.get(key)
    if hit and time.time() - hit[0] < 3:
        return [dict(x) for x in hit[1]]
    match = {"status": "available"}
    if category:
        match["category"] = category
    if year == "none":
        match["year"] = {"$in": [None, ""]}
    elif year:
        match["year"] = str(year)
    if server == 1:
        match["$or"] = [{"server": 1}, {"server": {"$exists": False}}]   # legacy stock counts as Server 1
    else:
        match["server"] = server
    counts = {}
    async for d in accounts_col.aggregate([{"$match": match}, {"$group": {"_id": "$country_code", "n": {"$sum": 1}}}]):
        counts[d["_id"]] = d["n"]
    result = []
    if counts:
        prices = {}
        if category:
            async for d in cat_prices_col.find({"category": category}):
                prices[d["code"]] = float(d["price"])
        async for c in countries_col.find({"is_active": True}):
            n = counts.get(c["code"], 0)
            if n > 0:
                result.append({"code": c["code"], "name": c["name"], "flag": c["flag"], "dial": c.get("dial"),
                               "price": prices.get(c["code"], c["price"]), "stock": n})
    if len(_ac_cache) > 500:
        _ac_cache.clear()
    _ac_cache[key] = (time.time(), result)
    return [dict(x) for x in result]

async def get_categories() -> List[dict]:
    cats = []
    async for cat in categories_col.find({"is_active": True}).sort("order", 1):
        cats.append(cat)
    return cats

# ─── 13. SESSION ZIP CONVERSION ────────────────────────────────
def _phone_from_filename(name: str) -> str:
    base   = os.path.splitext(os.path.basename(name))[0]
    digits = re.sub(r"[^\d]", "", base)
    return f"+{digits}" if len(digits) >= 7 else base

def _detect_session_format(session_bytes: bytes):
    import sqlite3, struct, ipaddress as _ip
    _DC_IP = {
        1: "149.154.175.53",
        2: "149.154.167.51",
        3: "149.154.175.100",
        4: "149.154.167.91",
        5: "91.108.56.130",
    }
    tmp = tempfile.NamedTemporaryFile(suffix=".session", delete=False)
    try:
        tmp.write(session_bytes)
        tmp.flush()
        tmp.close()
        conn = sqlite3.connect(tmp.name)
        cur  = conn.cursor()
        cur.execute("PRAGMA table_info(sessions)")
        cols = {row[1] for row in cur.fetchall()}
        if "server_address" in cols:
            cur.execute("SELECT dc_id, server_address, port, auth_key FROM sessions")
            row = cur.fetchone()
            conn.close()
            if row and row[3]:
                return "telethon", row[0], row[1], row[2], row[3]
        elif "user_id" in cols or "api_id" in cols:
            cur.execute("SELECT dc_id, auth_key FROM sessions")
            row = cur.fetchone()
            conn.close()
            if row and row[1]:
                dc_id  = row[0]
                server = _DC_IP.get(dc_id, _DC_IP[2])
                return "pyrogram", dc_id, server, 443, row[1]
        else:
            conn.close()
    except Exception as e:
        log.warning(f"[detect_fmt] sqlite error: {e}")
    finally:
        with contextlib.suppress(Exception):
            os.unlink(tmp.name)
    return None, None, None, None, None

def _pyrogram_to_telethon_ss(dc_id: int, server: str,
                              port: int, auth_key: bytes) -> Optional[str]:
    import struct, base64, ipaddress as _ip
    try:
        if not isinstance(auth_key, bytes) or len(auth_key) != 256:
            return None
        ip_bytes = _ip.ip_address(server).packed
        payload  = (
            struct.pack(">B", dc_id) +
            ip_bytes +
            struct.pack(">H", port) +
            auth_key
        )
        return "1" + base64.urlsafe_b64encode(payload).decode()
    except Exception as e:
        log.warning(f"[pyro→ss] build failed: {e}")
        return None

async def _session_file_to_string(session_bytes: bytes) -> Optional[str]:
    fmt, dc_id, server, port, auth_key = _detect_session_format(session_bytes)
    if fmt is None:
        return None
    ss = _pyrogram_to_telethon_ss(dc_id, server, port, auth_key)
    if ss:
        log.info(f"[zip] ✅ {fmt} session → StringSession")
    else:
        log.warning(f"[zip] ❌ Could not build StringSession for {fmt} session")
    return ss

# ─── 14. UPI QR ──────────────────────────────────────────────────
def _make_upi_qr(upi_id: str, amount: float, name: str) -> Optional[bytes]:
    try:
        import qrcode as qrc
        uri = (f"upi://pay?pa={_urlquote(str(upi_id))}&pn={_urlquote(str(name))}"
               f"&am={amount:.2f}&cu=INR&tn=Deposit")
        buf = io.BytesIO()
        qrc.make(uri).convert("RGB").save(buf, format="PNG")
        return buf.getvalue()
    except Exception as e:
        log.warning(f"[QR] Failed to generate UPI QR: {e}")
        return None

def _qr_card_png(uri: str) -> Optional[bytes]:
    """White card with a centered QR for ANY upi:// string (used for the Razorpay
    QR too — drawn locally, so Telegram never has to fetch an external image)."""
    try:
        import qrcode as qrc
        from PIL import Image, ImageDraw, ImageFont
        qr_img = qrc.make(uri).convert("RGB")
        qs = qr_img.size[0]
        pad, header_h, footer_h = 40, 90, 70
        W = qs + pad * 2
        H = header_h + qs + footer_h
        card = Image.new("RGB", (W, H), "white")
        draw = ImageDraw.Draw(card)
        draw.rectangle([0, 0, W, header_h], fill=(25, 45, 95))
        try:
            font_h = ImageFont.truetype("DejaVuSans-Bold.ttf", 26)
            font_f = ImageFont.truetype("DejaVuSans.ttf", 18)
        except Exception:
            font_h = font_f = ImageFont.load_default()
        title = "SCAN & PAY"
        tw = draw.textlength(title, font=font_h)
        draw.text(((W - tw) / 2, 28), title, font=font_h, fill="white")
        card.paste(qr_img, (pad, header_h))
        foot = "GPay  •  PhonePe  •  Paytm  •  BHIM"
        fw = draw.textlength(foot, font=font_f)
        draw.text(((W - fw) / 2, header_h + qs + 22), foot, font=font_f, fill=(60, 60, 60))
        buf = io.BytesIO()
        card.save(buf, format="PNG")
        return buf.getvalue()
    except Exception as e:
        log.warning(f"[QR] card render failed, plain QR used: {e}")
        try:
            import qrcode as qrc
            buf = io.BytesIO()
            qrc.make(uri).convert("RGB").save(buf, format="PNG")
            return buf.getvalue()
        except Exception as e2:
            log.error(f"[QR] could not render QR at all: {e2}")
            return None

def _make_polished_qr(upi_id: str, amount: float, name: str) -> Optional[bytes]:
    return _qr_card_png(f"upi://pay?pa={_urlquote(str(upi_id))}&pn={_urlquote(str(name))}"
                        f"&am={amount:.2f}&cu=INR&tn=Deposit")

# ─── 14b. REAL RAZORPAY DYNAMIC UPI QR (Auto-Verify) ────────────
_RZ_LAST_ERROR = ""

async def razorpay_create_qr(amount: float, dep_id: str, user_id: int) -> Optional[dict]:
    global _RZ_LAST_ERROR
    _RZ_LAST_ERROR = ""
    """Creates a single-use, fixed-amount Razorpay UPI QR for one deposit.
    Returns the Razorpay QR entity (has 'id', 'image_url', 'short_url'),
    or None if Razorpay isn't configured / the request failed."""
    if not RAZORPAY_KEY_ID or not RAZORPAY_KEY_SECRET:
        return None
    payload = {
        "type": "upi_qr",
        "name": f"Deposit {dep_id}",
        "usage": "single_use",
        "fixed_amount": True,
        "payment_amount": int(round(amount * 100)),
        "description": "Wallet top-up",
        "close_by": int(time.time()) + 1800,  # 30 min validity
        "notes": {"deposit_id": str(dep_id), "user_id": str(user_id)},
    }
    try:
        async with aiohttp.ClientSession(auth=aiohttp.BasicAuth(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET)) as s:
            async with s.post(f"{RAZORPAY_API_BASE}/payments/qr_codes", json=payload,
                               timeout=aiohttp.ClientTimeout(total=15)) as r:
                body = await r.json(content_type=None)
                if r.status not in (200, 201):
                    log.error(f"[Razorpay] QR create failed [{r.status}]: {body}")
                    err = (body.get("error") or {}) if isinstance(body, dict) else {}
                    _RZ_LAST_ERROR = f"HTTP {r.status}: {err.get('description') or err.get('code') or str(body)[:150]}"
                    return None
                return body
    except Exception as e:
        log.error(f"[Razorpay] QR create error: {e}")
        _RZ_LAST_ERROR = f"{type(e).__name__}: {e}"[:200]
        return None

async def razorpay_close_qr(qr_id: str):
    """Best-effort close so a paid/expired QR can't be reused."""
    if not qr_id or not RAZORPAY_KEY_ID or not RAZORPAY_KEY_SECRET:
        return
    try:
        async with aiohttp.ClientSession(auth=aiohttp.BasicAuth(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET)) as s:
            async with s.post(f"{RAZORPAY_API_BASE}/payments/qr_codes/{qr_id}/close",
                               timeout=aiohttp.ClientTimeout(total=10)) as r:
                if r.status not in (200, 201):
                    log.warning(f"[Razorpay] QR close failed [{r.status}] for {qr_id}")
    except Exception as e:
        log.warning(f"[Razorpay] QR close error for {qr_id}: {e}")

async def log_event(text: str):
    """Sends an event line to the admin log channel, if configured."""
    channel_id = LOGS_CHANNEL_ID or int(await get_setting("logs_channel_id", 0) or 0)
    if not channel_id:
        return
    buttons = None
    if text.lstrip().startswith(("🆕", "🛒")):        # New User / Purchase posts get an Open Bot button
        try:
            uname = await get_bot_username()
            if uname:
                buttons = [[url_btn("Buy Now", f"https://t.me/{uname}", "primary")]]
        except Exception:
            buttons = None
    try:
        await bot.send_message(channel_id, fancy(text), buttons=buttons)
    except Exception as e:
        log.warning(f"[log_channel] send failed: {e}")

# ─── 14c. TEMP-MESSAGE CLEANUP + UPI-APP PAY LINKS ─────────────
user_temp_msgs: Dict[int, List[int]] = {}
_qr_msgs: set = set()      # message ids of QR photos
_KEEP_TEMP_ON = {"upi_app", "check_payment", "deposit_paid", "store_noop"}

def _track_temp(user_id: int, msg) -> None:
    """Remember a helper message (QR image, info note) so it can be deleted later."""
    mid = getattr(msg, "id", None)
    if mid:
        user_temp_msgs.setdefault(user_id, []).append(mid)

async def _cleanup_temp(user_id: int) -> None:
    ids = user_temp_msgs.pop(user_id, [])
    if ids:
        try:
            await bot.delete_messages(user_id, ids)
        except Exception as e:
            log.debug(f"[cleanup] could not delete {ids}: {e}")

async def _delete_msg(user_id: int, msg_id) -> None:
    if not msg_id:
        return
    try:
        await bot.delete_messages(user_id, msg_id)
    except Exception:
        pass

_prompt_msg: Dict[int, int] = {}     # user_id -> message id of the "send the country name" prompt
_last_welcome: Dict[int, int] = {}   # user_id -> message id of the last /start welcome message

def _arm_prompt(user_id: int, event) -> None:
    mid = getattr(event, "message_id", None)
    if mid:
        _prompt_msg[user_id] = mid

def _consume_prompt(event, user_id: int) -> None:
    """After a typed search: auto-delete the user's text and the old prompt/list message
    (fire-and-forget, so the bot stays instant)."""
    ids = [event.message.id]
    old = _prompt_msg.pop(user_id, None)
    if old:
        ids.append(old)
    async def _go():
        try:
            await bot.delete_messages(user_id, ids)
        except Exception:
            pass
    asyncio.get_event_loop().create_task(_go())

async def _pay_app_button(user_id: int, link):
    """'Pay via UPI app' — a real URL button (opens the phone's UPI app through our
    /pay redirect page) when a public URL + upi:// link exist, else a callback fallback."""
    if link and str(link).startswith("upi://") and RENDER_EXTERNAL_URL:
        token = uuid.uuid4().hex[:16]
        try:
            await db["pay_links"].create_index("created_at", expireAfterSeconds=3600)
            await db["pay_links"].insert_one({"token": token, "link": link, "created_at": datetime.utcnow()})
            return url_btn("Pay via UPI app", f"{RENDER_EXTERNAL_URL.rstrip('/')}/pay/{token}", "success")
        except Exception as e:
            log.warning(f"[pay_link] could not create link: {e}")
    return color_btn("📲 Pay via UPI app", "upi_app", "default")

async def _deposit_buttons(user_id: int, link) -> list:
    return [
        [color_btn("✅ I Have Paid", "deposit_paid", "default")],
        [color_btn("❌ Cancel", "cancel_payment", "default")],
        [color_btn("◀️ Back", "deposit", "default")],
    ]

async def razorpay_qr_paid(qr_id: str, amount: float) -> bool:
    """Live check with Razorpay: has this single-use QR received the exact amount?"""
    if not qr_id or not RAZORPAY_KEY_ID or not RAZORPAY_KEY_SECRET:
        return False
    try:
        async with aiohttp.ClientSession(auth=aiohttp.BasicAuth(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET)) as s_:
            async with s_.get(f"{RAZORPAY_API_BASE}/payments/qr_codes/{qr_id}/payments",
                              timeout=aiohttp.ClientTimeout(total=15)) as r:
                if r.status != 200:
                    log.warning(f"[Razorpay] QR payments lookup [{r.status}] for {qr_id}")
                    return False
                body = await r.json()
        want = int(round(float(amount) * 100))
        return any(i.get("status") == "captured" and int(i.get("amount", 0)) == want
                   for i in body.get("items", []))
    except Exception as e:
        log.error(f"[Razorpay] QR payments lookup error: {e}")
        return False

async def _verify_deposit_ui(event, user_id: int) -> None:
    """'I Have Paid' / 'Check Payment' — verifies for real, never blind-approves."""
    from bson import ObjectId
    st = user_states.get(user_id, {})
    if st.get("state") == "await_deposit_screenshot":
        await event.answer("📸 Pay first, then send the payment screenshot here in the chat.", alert=True)
        return
    dep_id = st.get("deposit_id_obj")
    if not dep_id:
        last = await deposits_col.find_one(
            {"user_id": user_id, "method": {"$in": ["razorpay_auto", "razorpay_link"]}, "status": {"$in": ["pending", "approved"]}},
            sort=[("_id", -1)])
        if last:
            dep_id = str(last["_id"])
    if not dep_id:
        await event.answer("❌ No active deposit.", alert=True)
        return
    dep = await deposits_col.find_one({"_id": ObjectId(dep_id)})
    if not dep:
        await event.answer("❌ Deposit not found.", alert=True)
        return
    if dep.get("status") == "pending" and dep.get("method") in ("razorpay_auto", "razorpay_link"):
        pid = await razorpay_deposit_paid(dep)
        if pid:
            await _credit_deposit_by_id(dep["_id"], notify=False, delete_ui=False, payment_id=pid)
            dep = await deposits_col.find_one({"_id": dep["_id"]})
    status = dep.get("status")
    if status == "approved":
        await _cleanup_temp(user_id)
        user_states.pop(user_id, None)
        try:
            await event.delete()   # the button is on the QR photo — don't leave the QR behind
        except Exception:
            pass
        await bot.send_message(
            user_id,
            fancy(f"✅ **Payment confirmed!**\n\n`₹{dep.get('credits', 0)}` added to your wallet."),
            buttons=[[color_btn("🏠 Home", "main_menu", "default")]]
        )
    elif status == "pending":
        await event.answer("⏳ Payment not received yet. Wait 1–2 minutes and tap again.", alert=True)
    else:
        await event.answer(f"Status: {status}", alert=True)

async def _deposit_limits():
    """(minimum, maximum) deposit in Credits — editable from Admin → Settings."""
    try:
        mn = float(await get_setting("min_deposit", 10.0))
    except (TypeError, ValueError):
        mn = 10.0
    try:
        mx = float(await get_setting("max_deposit", 100000))
    except (TypeError, ValueError):
        mx = 100000.0
    return mn, max(mx, mn)

class _MsgUI:
    """Lets the callback-style deposit starters edit/delete a plain bot message
    (used after the user types a deposit amount)."""
    def __init__(self, msg, user_id: int):
        self._m = msg
        self._uid = user_id
        self.message_id = msg.id
    async def edit(self, *a, **kw):
        return await self._m.edit(*a, **kw)
    async def delete(self):
        return await self._m.delete()
    async def answer(self, text="", alert=False, **kw):
        if text:
            await bot.send_message(self._uid, text)

async def _blocking_pending_deposit(user_id: int):
    """Returns the user's pending deposit (auto or manual) if it's still within its
    15-minute window (and auto-expires it otherwise), so a user can't open two at once."""
    dep = await deposits_col.find_one(
        {"user_id": user_id, "status": "pending", "method": {"$in": ["razorpay_auto", "manual"]}},
        sort=[("_id", -1)]
    )
    if not dep:
        return None
    age = datetime.utcnow() - dep.get("created_at", datetime.utcnow())
    # A manual deposit the user never actually sent a screenshot for isn't a real
    # commitment yet (they may have just tapped Back) — quietly retire it instead
    # of forcing them through "Cancel This Deposit" to start a fresh one.
    if dep.get("method") == "manual" and not dep.get("screenshot_sent_at"):
        await deposits_col.update_one({"_id": dep["_id"]}, {"$set": {"status": "abandoned"}})
        return None
    if age > timedelta(minutes=15):
        await deposits_col.update_one({"_id": dep["_id"]}, {"$set": {"status": "expired"}})
        if dep.get("qr_code_id"):
            await razorpay_close_qr(dep["qr_code_id"])
        return None
    return dep

async def _show_pending_deposit_block(event, dep):
    submitted = dep.get("created_at", datetime.utcnow())
    await event.edit(
        fancy("⏳ **You already have a pending deposit**\n\n")
        + fancy_line("• amount: ") + f"`₹{dep['amount']:.2f}`\n"
        + fancy_line("• txn id: ") + f"`{dep.get('qr_code_id') or str(dep['_id'])}`\n"
        + fancy_line("• submitted: ") + f"`{submitted.strftime('%d/%m/%Y %H:%M')}`\n\n"
        + fancy_line("please wait for it to be approved. if you made a mistake and want to submit a new one, cancel this first."),
        buttons=[
            [color_btn("❌ Cancel This Deposit", "cancel_payment", "default")],
            [color_btn("◀️ Back", "deposit", "default")],
        ]
    )

async def _fetch_image_bytes(url: str) -> Optional[bytes]:
    """Download a (PNG/JPEG) image; None if it is not a normal raster image."""
    try:
        async with aiohttp.ClientSession() as sess:
            async with sess.get(url, timeout=aiohttp.ClientTimeout(total=15)) as r:
                if r.status != 200:
                    return None
                ctype = (r.headers.get("Content-Type") or "").lower()
                data = await r.read()
        if not ctype.startswith("image/") or "svg" in ctype or len(data) < 500:
            return None
        return data
    except Exception as e:
        log.warning(f"[Razorpay] QR image download failed: {e}")
        return None

async def _start_razorpay_auto_deposit(event, user_id: int, amount: float, credits: int):
    """Real dynamic UPI QR via Razorpay — credits ONLY after Razorpay confirms the
    payment (webhook, or a live check when the user taps 'I Have Paid')."""
    if not (RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET):
        await event.answer("❌ UPI / QR Auto is not set up yet. Please use Manual.", alert=True)
        return
    blocking = await _blocking_pending_deposit(user_id)
    if blocking:
        await _show_pending_deposit_block(event, blocking)
        return

    try:
        await event.edit("Creating your payment link…")
    except Exception:
        pass
    dep = await deposits_col.insert_one({
        "user_id": user_id, "amount": amount, "credits": credits,
        "method": "razorpay_auto", "status": "pending", "created_at": datetime.utcnow(),
    })
    dep_id = str(dep.inserted_id)
    qr = await razorpay_create_qr(amount, dep_id, user_id)
    if not qr or not qr.get("id"):
        await deposits_col.update_one({"_id": dep.inserted_id}, {"$set": {"status": "failed"}})
        extra = ""
        if await is_admin(user_id) and _RZ_LAST_ERROR:
            extra = f"\n\n🛠 Admin info: `{_RZ_LAST_ERROR}`"
        if _RZ_LAST_ERROR:
            await log_event(f"⚠️ **Razorpay QR failed**\n• `{_RZ_LAST_ERROR}`")
        await event.edit(fancy("❌ **Could not generate QR.**\n\nplease try manual method instead." + extra),
                         buttons=[[color_btn("◀️ Back", "deposit", "default")]])
        return

    content = qr.get("image_content")
    link = content if isinstance(content, str) and content.startswith("upi://") else None
    await deposits_col.update_one({"_id": dep.inserted_id}, {"$set": {
        "qr_code_id": qr["id"], "qr_image_url": qr.get("image_url"),
        "upi_link": link, "ui_msg_id": event.message_id,
    }})
    user_states[user_id] = {"deposit_id_obj": dep_id, "credits": credits, "amount": amount, "upi_link": link}

    msg = (
        fancy("⚡ **Scan & pay via UPI**\n\n")
        + fancy_line("• amount: ") + f"`₹{amount:.2f}`\n"
        + "\n"
        + fancy_line(
            "scan the qr code with any upi app (gpay, phonepe, paytm, bhim).\n"
            "funds are credited automatically the moment payment is received — no need to tap anything.\n\n"
            "💫 valid for 30 minutes."
        )
    )
    image_url = qr.get("image_url")
    buttons = await _deposit_buttons(user_id, link)
    # Razorpay's own branded QR card, downloaded and sent as a real PHOTO (big preview).
    # Passing the bare URL to Telegram turns it into a small "file" attachment.
    photo = await _fetch_image_bytes(image_url) if image_url else None
    png = None if photo else (_qr_card_png(link) if link else None)
    data = photo or png
    if data or image_url:
        try:
            await event.delete()
        except Exception:
            pass
        try:
            if data:
                qr_file = io.BytesIO(data)
                qr_file.name = "upi_qr.jpg" if data[:3] == b"\xff\xd8\xff" else "upi_qr.png"
                sent = await bot.send_file(user_id, qr_file, caption=msg, buttons=buttons, force_document=False)
            else:
                sent = await bot.send_file(user_id, image_url, caption=msg, buttons=buttons, force_document=False)
            _qr_msgs.add(sent.id)
            user_states[user_id]["ui_msg_id"] = sent.id
            await deposits_col.update_one({"_id": dep.inserted_id}, {"$set": {"ui_msg_id": sent.id}})
        except Exception as e:
            log.warning(f"[Razorpay] could not send QR photo+caption: {e}")
            await bot.send_message(user_id, msg + f"\n\n{qr.get('short_url', '')}", buttons=buttons)
    else:
        await event.edit(msg, buttons=buttons)

async def _start_manual_deposit(event, user_id: int, amount: float, credits: int):
    """UPI QR + screenshot + admin approval (no auto-credit possible here)."""
    upi_id = await get_setting("upi_id")
    upi_name = await get_setting("upi_name", "Prime Vault")
    if not upi_id:
        await event.answer("❌ UPI is not configured.", alert=True)
        return
    blocking = await _blocking_pending_deposit(user_id)
    if blocking:
        await _show_pending_deposit_block(event, blocking)
        return

    txn_id = f"DEP{datetime.utcnow().strftime('%y%m%d%H%M')}{uuid.uuid4().hex[:4].upper()}"
    link = (f"upi://pay?pa={upi_id}&pn={_urlquote(str(upi_name))}"
            f"&am={amount:.2f}&cu=INR&tn={txn_id}")
    dep = await deposits_col.insert_one({
        "user_id": user_id, "amount": amount, "credits": credits,
        "method": "manual", "txn_id": txn_id, "status": "pending",
        "created_at": datetime.utcnow(),
    })
    user_states[user_id] = {
        "state": "await_deposit_screenshot",
        "credits": credits, "amount": amount, "txn_id": txn_id,
        "upi_link": link, "ui_msg_id": event.message_id,
        "deposit_id_obj": str(dep.inserted_id),
    }
    msg = (
        fancy("📸 **UPI Manual Deposit**\n\n")
        + fancy_line("• amount: ") + f"`₹{amount:.2f}`\n"
        + fancy_line("• upi id: ") + f"`{upi_id}`\n"
        + fancy_line("• txn ref: ") + f"`{txn_id}`\n\n"
        + fancy_line(
            "scan the qr code with any upi app (gpay, phonepe, paytm, bhim) and pay the exact amount shown in the QR.\n"
            "then send the payment screenshot here — an admin will verify and approve it.\n\n"
            "💫 valid for 30 minutes."
        )
    )
    buttons = [
        [color_btn("❌ Cancel", "cancel_payment", "default")],
        [color_btn("◀️ Back", "deposit", "default")],
    ]
    try:
        qr = _make_upi_qr(upi_id, amount, upi_name)
    except Exception as e:
        log.error(f"[manual deposit] QR generation crashed: {e}")
        qr = None

    if qr:
        # One combined message — QR photo with the instructions as its caption —
        # instead of a text message followed by a separate QR message.
        try:
            await event.delete()
        except Exception:
            pass
        qr_file = io.BytesIO(qr)
        qr_file.name = "upi_qr.png"
        try:
            sent = await bot.send_file(user_id, qr_file, caption=msg, buttons=buttons)
            _qr_msgs.add(sent.id)
            user_states[user_id]["ui_msg_id"] = sent.id
        except Exception as e:
            log.error(f"[manual deposit] could not send QR photo+caption: {e}")
            await bot.send_message(user_id, msg, buttons=buttons)
    else:
        await event.edit(
            msg + "\n\n" + fancy(f"⚠️ **Couldn't render the QR image.** pay manually using UPI ID `{upi_id}`."),
            buttons=buttons
        )


# ─── 15. FANCY TYPOGRAPHY ───────────────────────────────────────
_SMALL_CAPS = {
    'a': 'ᴀ', 'b': 'ʙ', 'c': 'ᴄ', 'd': 'ᴅ', 'e': 'ᴇ',
    'f': 'ꜰ', 'g': 'ɢ', 'h': 'ʜ', 'i': 'ɪ', 'j': 'ᴊ',
    'k': 'ᴋ', 'l': 'ʟ', 'm': 'ᴍ', 'n': 'ɴ', 'o': 'ᴏ',
    'p': 'ᴘ', 'q': 'ǫ', 'r': 'ʀ', 's': 'ꜱ', 't': 'ᴛ',
    'u': 'ᴜ', 'v': 'ᴠ', 'w': 'ᴡ', 'x': 'x', 'y': 'ʏ',
    'z': 'ᴢ'
}
def _smallcaps_word(text: str) -> str:
    """True small-caps typography (big first letter per word, small-caps rest).
    Used ONLY by the category and country/stock/Buy buttons — everything else in
    the bot reads as normal text via the plain `fancy*` helpers below."""
    parts = text.split('`')
    for i in range(0, len(parts), 2):
        parts[i] = ''.join(_SMALL_CAPS.get(ch, ch) for ch in parts[i])
    return '`'.join(parts)

_KEEP_CAPS = {
    "otp": "OTP", "2fa": "2FA", "upi": "UPI", "qr": "QR", "vnh": "VNH", "id": "ID",
    "api": "API", "txid": "TXID", "gpay": "GPay", "phonepe": "PhonePe",
    "paytm": "Paytm", "bhim": "BHIM", "whatsapp": "WhatsApp", "telegram": "Telegram",
    "razorpay": "Razorpay", "usdt": "USDT",
}

def _tidy(line: str) -> str:
    """Capitalize the first letter of a line and restore known acronyms (OTP, UPI,
    2FA ...), leaving `backtick` spans (IDs, codes, links) exactly as written."""
    parts = line.split('`')
    for i in range(0, len(parts), 2):
        parts[i] = re.sub(r"\b([A-Za-z0-9]+)\b",
                          lambda m: _KEEP_CAPS.get(m.group(0).lower(), m.group(0)), parts[i])
    line = '`'.join(parts)
    m = re.search(r'[A-Za-z]', line)
    if m and (line[:m.start()].count('`') % 2 == 0):
        i = m.start()
        line = line[:i] + line[i].upper() + line[i+1:]
    return line

def fancy(text: str) -> str:
    """Plain, normal text (headings use ordinary **bold** markdown): every line starts
    with a capital and known acronyms are restored."""
    return "\n".join(_tidy(l) for l in text.split("\n"))

def fancy_caps(text: str) -> str:
    return fancy(text)

def fancy_line(text: str) -> str:
    return fancy(text)

_BUTTON_NORMAL = {value: key.upper() for key, value in _SMALL_CAPS.items()}
_BUTTON_NORMAL['s'] = 'S'   # older hard-coded strings use a plain 's' inside small-caps words
_SC_MARKERS = {value for key, value in _SMALL_CAPS.items() if value != key}
def button_label(text: str) -> str:
    """Buttons: words written in small caps become full-size CAPS; ordinary
    words (admin-typed category/country names, plain Title Case labels) are left as typed."""
    out = []
    for word in re.split(r'( )', text):
        if any(ch in _SC_MARKERS for ch in word):
            out.append(''.join(_BUTTON_NORMAL.get(ch, ch) for ch in word))
        else:
            out.append(word)
    return ''.join(out)

# ─── 16. KEYBOARD BUILDERS ──────────────────────────────────────
# FIXED: Use Button.inline with style argument (supports colored buttons)
def _mk_btn(text, data, style="default"):
    """Every button: emoji-free label + colour (green / blue / red).
    style="default" -> colour is picked from the label (Back/Home/Buy = green,
    Cancel/Delete/Terms = red, everything else = blue)."""
    label = strip_emoji(text) or "·"
    force = isinstance(style, str) and style.endswith("!")
    if force:
        style = style[:-1]
    st = resolve_style(style, label)
    _low = label.lower().strip()
    if force:
        pass                                             # explicit colour (table screens)
    elif re.fullmatch(r"(home|main menu)", _low):
        st = STYLE_RED                                   # Home / Main Menu -> always red
    elif _low.startswith("back") or any(m in str(text) for m in ("\U0001F519", "\u25C0", "\u2B05")):
        st = STYLE_BLUE                                  # Back (any kind) -> always blue
    try:
        return Button.inline(label, data, style=st)
    except TypeError:                       # Telethon build without coloured buttons
        return Button.inline(label, data)

def color_btn(text, data, style="default"):
    return _mk_btn(button_label(text), data, style)

def color_btn_raw(text, data, style="default"):
    return _mk_btn(text, data, style)

def _norm_link(link: str) -> str:
    link = (link or "").strip()
    if link.startswith("@"):
        return "https://t.me/" + link[1:]
    if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{3,}", link):
        return "https://t.me/" + link
    if link and not re.match(r"^(https?://|tg://)", link):
        return "https://" + link
    return link

def url_btn(text, url, style="primary"):
    label = strip_emoji(button_label(text)) or "Open"
    st = resolve_style(style, label)
    try:
        return Button.url(label, url, style=st)
    except TypeError:
        return Button.url(label, url)

async def main_menu_buttons(user_id: int) -> list:
    rows = [[color_btn("Browse Accounts", "store", "success")]]
    rows.append([
        color_btn("Wallet", "balance", "primary"),
        color_btn("My Orders", "orders", "primary"),
    ])
    rows.append([color_btn("Profile", "profile", "primary")])
    support = _norm_link(await get_setting("support_link", "") or "")
    rows.append([
        color_btn("Referral", "referral", "primary"),
        url_btn("Support", support) if support else color_btn("Support", "help", "primary"),
    ])
    if await get_setting("whatsapp_enabled", False):
        rows.append([color_btn("Buy WhatsApp", "whatsapp", "primary")])
    rows.append([color_btn("Terms of Service", "show_terms", "danger")])
    if await is_admin(user_id):
        rows.append([color_btn("Admin Panel", "admin", "primary")])
    return rows

async def _per_row() -> int:
    try:
        return max(1, min(4, int(await get_setting("buttons_per_row", 1))))
    except (TypeError, ValueError):
        return 1

async def _category_buttons(categories: List[dict], back_data: str = "store", server: int = 1) -> list:
    rows = []
    per_row = 2
    stock_filter = (
        {"$or": [{"server": 1}, {"server": {"$exists": False}}]} if server == 1
        else {"server": server}
    )
    counts = {}
    async for d in accounts_col.aggregate([{"$match": {"status": "available", **stock_filter}},
                                           {"$group": {"_id": "$category", "n": {"$sum": 1}}}]):
        counts[d["_id"]] = d["n"]
    row = []
    for cat in categories:  # admin's own order is kept — not re-sorted by stock
        name = str(cat.get("name", "Category")).strip()
        row.append(plain_btn(f"{fancy_btn(name)} ({counts.get(name, 0)})", f"category:{name}"))
        if len(row) == per_row:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    rows.append([plain_btn(fancy_btn("Back"), back_data), plain_btn(fancy_btn("Home"), "main_menu")])
    return rows

def plain(text: str) -> str:
    """Message in the clean look: real bold + normal text, emoji kept (no small-caps / math fonts)."""
    return PLAIN + text

def green_btn(text, data):
    """Green button, emoji kept, normal font."""
    try:
        return Button.inline(text, data, style=STYLE_GREEN)
    except TypeError:
        return Button.inline(text, data)

_DIAL = dict(x.split("=") for x in (
    "AF=93 AL=355 DZ=213 AS=1684 AD=376 AO=244 AI=1264 AG=1268 AR=54 AM=374 AW=297 AU=61 AT=43 AZ=994 BS=1242 BH=973 "
    "BD=880 BB=1246 BY=375 BE=32 BZ=501 BJ=229 BM=1441 BT=975 BO=591 BA=387 BW=267 BR=55 BN=673 BG=359 BF=226 BI=257 "
    "KH=855 CM=237 CA=1 CV=238 KY=1345 CF=236 TD=235 CL=56 CN=86 CO=57 KM=269 CG=242 CD=243 CR=506 CI=225 HR=385 CU=53 "
    "CY=357 CZ=420 DK=45 DJ=253 DM=1767 DO=1809 EC=593 EG=20 SV=503 GQ=240 ER=291 EE=372 SZ=268 ET=251 FJ=679 FI=358 "
    "FR=33 GF=594 PF=689 GA=241 GM=220 GE=995 DE=49 GH=233 GI=350 GR=30 GL=299 GD=1473 GP=590 GU=1671 GT=502 GN=224 "
    "GW=245 GY=592 HT=509 HN=504 HK=852 HU=36 IS=354 IN=91 ID=62 IR=98 IQ=964 IE=353 IL=972 IT=39 JM=1876 JP=81 JO=962 "
    "KZ=7 KE=254 KI=686 KP=850 KR=82 KW=965 KG=996 LA=856 LV=371 LB=961 LS=266 LR=231 LY=218 LI=423 LT=370 LU=352 "
    "MO=853 MG=261 MW=265 MY=60 MV=960 ML=223 MT=356 MQ=596 MR=222 MU=230 MX=52 FM=691 MD=373 MC=377 MN=976 ME=382 "
    "MA=212 MZ=258 MM=95 NA=264 NR=674 NP=977 NL=31 NC=687 NZ=64 NI=505 NE=227 NG=234 MK=389 NO=47 OM=968 PK=92 PW=680 "
    "PS=970 PA=507 PG=675 PY=595 PE=51 PH=63 PL=48 PT=351 PR=1787 QA=974 RE=262 RO=40 RU=7 RW=250 KN=1869 LC=1758 "
    "VC=1784 WS=685 SM=378 ST=239 SA=966 SN=221 RS=381 SC=248 SL=232 SG=65 SK=421 SI=386 SB=677 SO=252 ZA=27 SS=211 "
    "ES=34 LK=94 SD=249 SR=597 SE=46 CH=41 SY=963 TW=886 TJ=992 TZ=255 TH=66 TL=670 TG=228 TO=676 TT=1868 TN=216 TR=90 "
    "TM=993 UG=256 UA=380 AE=971 GB=44 US=1 UY=598 UZ=998 VU=678 VA=379 VE=58 VN=84 VG=1284 VI=1340 YE=967 ZM=260 "
    "ZW=263 XK=383").split())

def styled_btn(text, data, style):
    """Coloured button (emoji kept, normal font). style: STYLE_GREEN / STYLE_BLUE / STYLE_RED."""
    try:
        return Button.inline(text, data, style=style)
    except TypeError:
        return Button.inline(text, data)

def blue_btn(text, data):
    """Blue button, emoji kept, normal font."""
    try:
        return Button.inline(text, data, style=STYLE_BLUE)
    except TypeError:
        return Button.inline(text, data)

def _flag_for_name(name: str) -> str:
    r = resolve_country(name or "")
    return r.get("flag") if r.get("code") else "🌍"

def _pack_btns(items, short_len: int = 19) -> list:
    """items = [(label, data)].  Short labels go two per row, long ones get a full row (full name always shown)."""
    rows, pending = [], None
    for label, data in items:
        b = blue_btn(label, data)
        if len(label) > short_len:
            if pending is not None:
                rows.append([pending])
                pending = None
            rows.append([b])
        elif pending is None:
            pending = b
        else:
            rows.append([pending, b])
            pending = None
    if pending is not None:
        rows.append([pending])
    return rows

def fancy_btn(text) -> str:
    """Small-caps button text. Only the first word starts with a capital:  India Spam -> Iɴᴅɪᴀ ꜱᴘᴀᴍ"""
    def sc(w):
        return "".join(_SMALL_CAPS.get(ch, ch) for ch in w.lower())
    out, first = [], True
    for w in str(text).split(" "):
        if w and w[0].isalpha():
            out.append(w[0].upper() + sc(w[1:]) if first else sc(w))
            first = False
        else:
            out.append(sc(w))
    return " ".join(out)

_UI = {"flags": True}          # admin switch: show country flags on buttons

def _fl(flag) -> str:
    return f"{flag} " if (_UI["flags"] and flag) else ""

async def _load_ui_flags():
    _UI["flags"] = bool(await get_setting("show_flags", True))

def plain_btn(text, data):
    """Uncoloured button (Telegram's normal look) — label is used exactly as given (emoji kept)."""
    try:
        return Button.inline(text, data)
    except Exception:
        return Button.inline(str(text), data)

def buy_btn(data):
    """Green  Bᴜʏ ✅  button."""
    label = fancy_btn("Buy") + " ✅"
    try:
        return Button.inline(label, data, style=STYLE_GREEN)
    except TypeError:
        return Button.inline(label, data)

def _tbl_row(name: str, price_txt: str, qty, data, flag: str = "") -> list:
    """One country:  [ Iɴᴅɪᴀ (20) ]  [ ₹44 ]  [ Bᴜʏ ✅ ]   — first two uncoloured, Buy green."""
    n = str(name)
    n = n if len(n) <= 12 else n[:11] + "…"
    return [plain_btn(f"{fancy_btn(n)} ({qty})", data),
            plain_btn(f"₹{price_txt}", data),
            buy_btn(data)]

def _page_row(page: int, pages: int, cb, noop, style: str = "primary") -> list:
    """Numbered pages like  [1] 2 3 4 5 6 7  (current page in brackets, window of 7)."""
    n = 7
    first = max(0, min(page - n // 2, pages - n))
    last = min(pages, first + n)
    row = []
    for i in range(first, last):
        if i == page:
            row.append(color_btn_raw(f"[{i+1}]", noop, style))
        else:
            row.append(color_btn_raw(str(i + 1), cb(i), style))
    return row

def _sorted_countries(countries: List[dict], sort: str = "asc") -> List[dict]:
    return sorted(countries, key=lambda c: (float(c.get("price", 0) or 0), str(c.get("name", "")).lower()),
                  reverse=(sort == "desc"))

def _country_label(c: dict) -> str:
    """🇮🇳 Iɴᴅɪᴀ+91 ¦ ₹44   — the +code only appears when the admin has set one."""
    d = str(c.get("dial") or "").lstrip("+").strip()
    return f"{_fl(c.get('flag', ''))}{fancy_btn(c['name'])}{'+' + d if d else ''} ¦ ₹{c['price']:g}"

def _inventory_lines(countries: List[dict], page: int = 0, per_page: int = 16, sort: str = "asc") -> List[str]:
    """Message lines (full name + price + stock) for the countries on this page."""
    cs = _sorted_countries(countries, sort)
    pages = max(1, (len(cs) - 1) // per_page + 1)
    page = max(0, min(page, pages - 1))
    return [f"{c.get('flag', '')} {c['name']} — ₹{c['price']:g} — Stock: {c['stock']:,}"
            for c in cs[page * per_page: page * per_page + per_page]]

def _inventory_buttons(countries: List[dict], page: int = 0, per_page: int = 16, per_row: int = 2,
                       back_data: str = "store", sort: str = "asc") -> list:
    countries = _sorted_countries(countries, sort)
    total = len(countries)
    pages = max(1, (total - 1) // per_page + 1)
    page = max(0, min(page, pages - 1))
    chunk = countries[page * per_page: page * per_page + per_page]
    rows = _pack_btns([(_country_label(c), f"buy:{c['code']}") for c in chunk], short_len=22)
    if pages > 1:
        rows.append(_page_row(page, pages, lambda i: f"store_page:{i}", "store_noop", style="danger"))
        rows.append([styled_btn("← " + fancy_btn("Back"), back_data, STYLE_GREEN),
                     styled_btn(fancy_btn("Search"), "store_search", STYLE_GREEN),
                     styled_btn(fancy_btn("Filters"), "cf", STYLE_GREEN)])
    else:
        rows.append([styled_btn("← " + fancy_btn("Back"), back_data, STYLE_GREEN),
                     styled_btn(fancy_btn("Filters"), "cf", STYLE_GREEN)])
    if total > 1:
        rows.append([styled_btn(fancy_btn("Sort · Price · " + ("High to Low" if sort == "desc" else "Low to High")),
                                "store_sort", STYLE_GREEN)])
    rows.append([styled_btn(fancy_btn("Home"), "main_menu", STYLE_RED)])
    return rows

def _admin_menu_buttons(is_owner_flag: bool) -> list:
    rows = [
        [color_btn("📊 Stats", "astats", "default")],
        [color_btn("📦 Upload Sessions", "upload_sessions", "default"),
         color_btn("📋 Session Overview", "manage_sessions", "default")],
        [color_btn("💳 Pending Deposits", "pending_deposits", "default")],
        [color_btn("📢 Broadcast", "broadcast", "default")],
        [color_btn("⚙️ Settings", "asettings", "default"),
         color_btn("🌍 Countries", "acountries", "default")],
        [color_btn("🗂️ Categories", "acategories", "default")],
        [color_btn("👤 Users", "ausers", "default"),
         color_btn("💰 Add Balance", "admin_add_bal", "default")],
    ]
    if is_owner_flag:
        rows.append([color_btn("🔑 Manage Admins", "manage_admins", "default")])
    rows.append([color_btn("🏠 Home", "main_menu", "default")])
    return rows

DEFAULT_TERMS_TEXT = (
    "⚠️ **Terms & Conditions**\n"
    "━━━━━━━━━━━━━━━━━━\n"
    "Please read and accept our terms to use this bot:\n\n"
    "📍 **Account policy**\n"
    "• These accounts are for testing / educational purposes.\n"
    "• We are **not** responsible for any ban or freeze after login.\n"
    "• Use Telegram X or an official app for best stability.\n\n"
    "💰 **Refund policy**\n"
    "• **No refunds** under any circumstances, except 'No OTP received'.\n"
    "• All sales are final — buy at your own risk.\n\n"
    "🚫 **Misuse:** any illegal activity will result in a ban.\n\n"
    "__By tapping 'Accept', you agree to all the terms above.__"
)

LINE = "━━━━━━━━━━━━━━━━━━"

def _clean_md(txt: str) -> str:
    return re.sub(r"[*_`\[\]]", "", txt or "").strip()

async def _welcome_text(user_id: int, first_name: str) -> str:
    first_name = _clean_md(first_name) or "User"
    user = await users_col.find_one({"user_id": user_id}) or {}
    bal = float(user.get("balance", 0))
    bot_name = (_clean_md(str(await get_setting("bot_name", "Prime Vault"))) or "Prime Vault").upper()
    return (
        RAW
        + f"**{bot_name}**\n"
        "__PREMIUM TELEGRAM ACCOUNT STORE__\n"
        f"{LINE}\n"
        f"Welcome, **{first_name}**\n\n"
        f"> USER ID · `{user_id}`\n"
        f"> BALANCE · `₹{bal:.2f}`\n"
        f"{LINE}\n"
        "__Browse and purchase verified Telegram accounts.__\n"
        "__Instant delivery · Secure checkout · 24/7 support__"
    )

async def _send_main_welcome(event, user_id: int):
    sender = await event.get_sender()
    welcome_msg = await _welcome_text(user_id, getattr(sender, "first_name", None))
    photo_id = await get_setting("welcome_photo")
    old_ids = []
    if _last_welcome.get(user_id):
        old_ids.append(_last_welcome.pop(user_id))
    if getattr(event, "message", None) is not None and getattr(event.message, "id", None) and not hasattr(event, "data"):
        old_ids.append(event.message.id)          # the user's own /start command
    sent = None
    if photo_id:
        try:
            sent = await event.respond(file=photo_id, message=welcome_msg, buttons=await main_menu_buttons(user_id))
        except Exception:
            sent = None
    if sent is None:
        sent = await event.respond(welcome_msg, buttons=await main_menu_buttons(user_id))
    if getattr(sent, "id", None):
        _last_welcome[user_id] = sent.id
    if old_ids:
        async def _del():
            try:
                await bot.delete_messages(user_id, old_ids)
            except Exception:
                pass
        asyncio.get_event_loop().create_task(_del())

# ─── 17. /start COMMAND ─────────────────────────────────────────
@bot.on(events.NewMessage(pattern="/start"))
async def cmd_start(event):
    user_id     = event.sender_id
    args        = event.message.text.split()
    payload     = args[1].strip() if len(args) > 1 else ""
    sender      = await event.get_sender()
    user = await register_start_user(user_id, payload, sender)
    if user.get("is_banned"):
        await event.respond("🚫 You are banned from this bot.")
        return
    if not await is_user_member(user_id):
        await send_join_message(event)
        return
    # Join reward only after every required join is verified (once-only claim).
    try:
        await award_referral_signup_bonus(user_id)
    except Exception:
        log.exception(f"Could not process signup referral for {user_id}")
    if payload.startswith("stk_") and user.get("accepted_terms"):
        if await open_stock_deeplink(event, user_id, payload):
            return
    await _start_flow(event, user_id, user)

async def _start_flow(event, user_id: int, user: dict):
    """Terms & Conditions for new users, otherwise the main menu (shared by /start and Check Again)."""
    if not user.get("accepted_terms"):
        terms_text = await get_setting("terms_text") or DEFAULT_TERMS_TEXT
        await event.respond(
            fancy_caps(terms_text),
            buttons=[
                [color_btn("✅ Accept", "terms_accept", "default"),
                 color_btn("❌ Reject", "terms_decline", "default")],
            ]
        )
        return
    await _send_main_welcome(event, user_id)



# ─── 17b. BROWSE / UPLOAD HELPERS ──────────────────────────────
DEFAULT_SERVER_LABELS = {
    "1": {"tag": "Private Stock", "bullets": [
        "Cheapest option",
        "Directly managed private stock",
        "Limited stock may vary by country",
    ]},
    "3": {"tag": "Live Provider Server", "bullets": [
        "Two providers with live stock and live prices",
        "Quote is locked for 2 minutes before you pay",
        "Automatic refund to your wallet if the supplier fails",
    ]},
    "2": {"tag": "External Server", "bullets": [
        "Accounts are sourced from a third-party server",
        "More countries and stock may be available",
        "Price depends on live server rates",
        "Third-party terms apply",
    ]},
}

def _vnh_fetch_value(d: dict, *keys):
    for k in keys:
        if isinstance(d, dict) and d.get(k) not in (None, ""):
            return d[k]
    return None

async def _send_vnh_country_list(event, user_id: int, page: int, search: str = None):
    countries = await vnh_server.available_countries()
    if search:
        s_ = search.strip().lower()
        countries = [c for c in countries if s_ in c["name"].lower() or s_ in c["code"].lower()]
    if not countries:
        await event.edit(
            plain("😔 **No countries found.**\n\nThe supplier has no stock right now, or no country matched your search."),
            buttons=[[plain_btn(fancy_btn("Back to servers"), "store")]]
        )
        return
    per_page = 8
    pages = (len(countries) - 1) // per_page + 1
    page = max(0, min(page, pages - 1))
    _st = user_states.get(user_id)
    if not isinstance(_st, dict):
        _st = user_states[user_id] = {}
    _st.pop("state", None)
    _st["vnh_search"] = search or None
    _st["vnh_page"] = page
    chunk = countries[page * per_page: page * per_page + per_page]
    async def _vp(c_):
        if c_.get("price") is None:
            return "--"
        try:
            return f"{(await vnh_server.calculate_price(float(c_['price'])))['retail_inr']:.0f}"
        except Exception:
            return "--"
    ptxts = await asyncio.gather(*[_vp(c_) for c_ in chunk])        # all prices at once
    flags_ = [c.get("flag") or _flag_for_name(c["name"]) for c in chunk]
    rows = _pack_btns([(f"{_fl(fl)}{fancy_btn(c['name'])} ¦ ₹{pt}", f"vnh_country:{c['code']}") for c, pt, fl in zip(chunk, ptxts, flags_)], short_len=22)
    lines_ = [f"{fl} {c['name']} — ₹{pt} — Stock: {int(c.get('qty', 0) or 0):,}" for c, pt, fl in zip(chunk, ptxts, flags_)]
    if pages > 1:
        rows.append(_page_row(page, pages, lambda i: f"vnh_page:{i}", "store_noop", style="danger"))
        rows.append([styled_btn("← " + fancy_btn("Back to servers"), "store", STYLE_GREEN),
                     styled_btn(fancy_btn("Search"), "vnh_search", STYLE_GREEN)])
    else:
        rows.append([styled_btn("← " + fancy_btn("Back to servers"), "store", STYLE_GREEN)])
    await event.edit(
        plain(f"🛍️ **Available Telegram services**\n\n" + "\n".join(lines_) + f"\n\n📄 Page {page+1}/{pages}"),
        buttons=rows
    )

async def _enter_server(event, user_id: int, server_num: int):
    """Shared by tapping a server button and the single-active-server auto-skip."""
    if server_num == SERVER3_NUMBER and server_num != int(await get_setting("vnh_server_number", 2)):
        if not server3_server.configured:
            await event.edit(
                fancy("⚠️ **This Server isn't connected yet.**\n\nThe admin needs to add SERVER3_API_KEY before this server can be used. Please try server 1."),
                buttons=[[color_btn("◀️ Back", "store", "default")]])
            return
        await handle_server3_callback(event, "server3", user_id)
        return
    if server_num == int(await get_setting("vnh_server_number", 2)):
        if not vnh_server.configured:
            await event.edit(
                fancy("⚠️ **This Server isn't connected yet.**\n\n")
                + fancy_line("the admin needs to add a vnh api key before this server can be used. please try server 1."),
                buttons=[[color_btn("◀️ Back", "store", "default")]]
            )
            return
        await _send_vnh_country_list(event, user_id, 0)
        return
    cats = await get_categories()
    await event.edit(
        plain(f"📂 **Select account category** · Server {server_num}\n\n"
              "Choose the category that best fits your need.\n"
              "• Stock & price are shown before purchase\n"
              "• Each category opens its available countries\n\n"
              "👇 Tap a category below:"),
        buttons=await _category_buttons(cats, back_data="store", server=server_num)
    )

async def _server_active(server: int) -> bool:
    active = await get_setting("server_active", None)
    active = active if isinstance(active, dict) else {}
    if str(server) in active:
        return bool(active[str(server)])
    if server == 1:
        return True
    if server == SERVER3_NUMBER and server3_server.configured:
        return True
    try:
        vnh_no = int(await get_setting("vnh_server_number", 2))
    except (TypeError, ValueError):
        vnh_no = 2
    return server == vnh_no and vnh_server.configured     # on by default once the VNH key is set

async def _server_label(server: int) -> dict:
    labels = await get_setting("server_labels", None)
    labels = labels if isinstance(labels, dict) else {}
    custom = labels.get(str(server))
    if isinstance(custom, dict) and custom.get("bullets"):
        return custom
    default = DEFAULT_SERVER_LABELS.get(str(server))
    if default:
        return default
    return {"tag": "Extra Stock", "bullets": ["Instant delivery"]}

async def _server_year_cfg(server: int) -> dict:
    all_cfg = await get_setting("server_year_config", None)
    all_cfg = all_cfg if isinstance(all_cfg, dict) else {}
    cfg = all_cfg.get(str(server)) or {}
    years = cfg.get("years")
    if not isinstance(years, list) or not years:
        years = [str(y) for y in range(2015, 2027)]
    return {"enabled": bool(cfg.get("enabled", False)), "years": [str(y) for y in years]}

_cat_year_cache: Dict[str, bool] = {}

async def _cat_has_year(cat_name: str) -> bool:
    """Year step belongs to the CATEGORY (Old Accounts ON by default; admin can switch any category)."""
    v = _cat_year_cache.get(cat_name)
    if v is not None:
        return v
    doc = await categories_col.find_one({"name": cat_name}, {"has_year": 1})
    if doc is not None and doc.get("has_year") is not None:
        v = bool(doc["has_year"])
    else:
        v = "old" in (cat_name or "").lower()
    _cat_year_cache[cat_name] = v
    return v

async def _set_server_year_cfg(server: int, **kwargs) -> None:
    all_cfg = await get_setting("server_year_config", None)
    all_cfg = all_cfg if isinstance(all_cfg, dict) else {}
    cur = all_cfg.get(str(server)) or {}
    cur.update(kwargs)
    all_cfg[str(server)] = cur
    await set_setting("server_year_config", all_cfg)

async def _send_country_list(event, user_id: int, page: int = 0):
    st = user_states.get(user_id, {})
    cat_name = st.get("category")
    server = st.get("server", 1)
    year = st.get("year")
    countries = await get_active_countries(cat_name, server=server, year=year)
    back = f"category:{cat_name}" if (year and cat_name) else f"server:{server}"
    st["list_page"] = page
    _ms = int(st.get("min_stock", 0) or 0)
    if _ms and countries:
        countries = [c for c in countries if c["stock"] >= _ms]
        if not countries:
            await event.edit(
                plain(f"😔 **No country has {_ms}+ accounts right now.**\n\nChange the filter to see more."),
                buttons=[[styled_btn(fancy_btn("Filters"), "cf", STYLE_GREEN)],
                         [styled_btn("← " + fancy_btn("Back"), back, STYLE_GREEN)]])
            return
    q = str(st.get("search") or "").strip().lower()
    if q and countries:
        countries = [c for c in countries if q in c["name"].lower() or q in c["code"].lower()]
        if not countries:
            await event.edit(
                plain(f"😔 **No country found for `{q}`.**\n\n• Try another name"),
                buttons=[[color_btn("Search Country", "store_search", "primary")],
                         [color_btn("◀️ Back", back, "default")],
                         [color_btn("🏠 Home", "main_menu", "default")]])
            return
    if not countries:
        await event.edit(
            plain(
                f"😔 **No accounts available in '{cat_name}'{' (' + str(year) + ')' if year else ''}.**\n\n"
                "• This option is currently out of stock\n"
                "• Please choose another option to continue"
            ),
            buttons=[[color_btn("◀️ Back", back, "default")]]
        )
        return
    title = f"{cat_name} • {year}" if year else f"{cat_name}"
    await event.edit(
        plain(
            f"📌 **{title}**\n\n"
            + "\n".join(_inventory_lines(countries, page, sort=st.get("sort", "asc")))
            + "\n\n👇 Tap a country to see its stock:"
        ),
        buttons=_inventory_buttons(countries, page, back_data=back, sort=st.get("sort", "asc"))
    )

async def _price_gate(event, user_id: int, srv_n, cc: str, cat_name: str, year=None):
    """Price belongs to (country + category). Asked on EVERY upload; you can keep the current one or type a new one."""
    c = await countries_col.find_one({"code": cc})
    if not c:
        await event.answer("❌ Country not found.", alert=True)
        return
    cur = await get_cat_price(cc, cat_name, None)
    default = cur if cur is not None else float(c.get("price", 0) or 0)
    user_states[user_id] = {"state": "set_cat_price", "srv": srv_n, "cc": cc, "cat": cat_name,
                            "year": year, "default": default}
    rows = []
    if default > 0:
        rows.append([color_btn(f"✅ Keep ₹{default:g}", "cp_use", "default")])
    rows.append([color_btn("❌ Cancel", "admin", "default")])
    await event.edit(fancy(
        f"💰 **Set price**\n\n• Country: **{c['name']}**\n• Category: **{cat_name}**\n"
        + (f"• Current: `₹{default:g}`\n" if default > 0 else "")
        + "\nSend the price in ₹ for this country in this category.\n"
        "Other categories keep their own price."), buttons=rows)

async def _begin_upload(event, user_id: int, srv_n, cc: str, cat_name: str, year=None):
    c = await countries_col.find_one({"code": cc})
    if not c:
        await event.answer("❌ Country not found.", alert=True)
        return
    user_states[user_id] = {
        "state": "waiting_zip",
        "country_code": cc,
        "country_name": c["name"],
        "price": float(await get_cat_price(cc, cat_name, c["price"])),
        "category": cat_name,
        "server": int(srv_n),
        "year": str(year) if year else None,
        "twofa_password": "",
    }
    default_2fa = await get_setting("default_2fa", "")
    hint = f"\n\n💡 Default 2FA: `{default_2fa}`" if default_2fa else ""
    yr = f" • {year}" if year else ""
    await event.edit(
        fancy(
            f"📦 **Upload Sessions — {c['flag']} {c['name']} ({cat_name}{yr}) • Server {srv_n}**\n\n"
            "Step 1 (optional): send 2FA password as text.\n"
            f"If not sent, default 2FA will be used.{hint}\n"
            "Step 2: send the **.zip** or **.session** file."
        ),
        buttons=[[color_btn("❌ Cancel", "admin", "default")]],
    )

# ─── 18. CALLBACK ROUTER ────────────────────────────────────────
_PHOTO_KEEP = {"upi_app", "check_payment", "deposit_paid", "cancel_payment", "store_noop"}

class _EditAsNew:
    """Wraps a callback event whose message was deleted: .edit() sends a new message."""
    def __init__(self, ev):
        self._ev = ev
    def __getattr__(self, name):
        return getattr(self._ev, name)
    async def edit(self, *args, **kwargs):
        return await bot.send_message(self._ev.sender_id, *args, **kwargs)
    async def delete(self):
        return None

@bot.on(events.CallbackQuery())
async def callback_router(event, data_override=None):
    data    = data_override or (event.data.decode() if isinstance(event.data, bytes) else event.data)
    user_id = event.sender_id

    if data == "check_join":
        user, member_ok = await users_col.find_one({"user_id": user_id}), True
    else:                                        # user lookup + force-join check run at the same time
        user, member_ok = await asyncio.gather(users_col.find_one({"user_id": user_id}), is_user_member(user_id))
    if user and user.get("is_banned"):
        await event.answer("🚫 You are banned.", alert=True)
        return

    if not member_ok:
        await event.answer("❌ Join required channels first!", alert=True)
        return

    # Any helper messages (QR image, notes) from the previous screen are no longer needed.
    if data not in _KEEP_TEMP_ON:
        await _cleanup_temp(user_id)

    # Leaving a QR photo screen: delete the photo and show the next screen as a fresh message
    # (editing a photo message would leave the QR image behind).
    if (not isinstance(event, _EditAsNew) and data not in _PHOTO_KEEP
            and event.message_id in _qr_msgs):
        _qr_msgs.discard(event.message_id)
        try:
            await event.delete()
        except Exception:
            pass
        event = _EditAsNew(event)

    # ── ported features (Server 3, bulk, referral, payment control, sessions, admin) ──
    if await ext_callback(event, data, user_id, user):
        return

    # ── MAIN MENU ────────────────────────────────────────────────
    if data == "main_menu":
        user_states.pop(user_id, None)
        sender = await event.get_sender()
        await event.edit(
            await _welcome_text(user_id, getattr(sender, "first_name", None)),
            buttons=await main_menu_buttons(user_id),
        )

    # ── CHECK JOIN ───────────────────────────────────────────────
    elif data == "check_join":
        if await is_user_member(user_id):
            asyncio.get_event_loop().create_task(safe_callback_answer(event, "✅ Verified!"))
            try:
                await award_referral_signup_bonus(user_id)
            except Exception:
                log.exception(f"Could not process verified join referral for {user_id}")
            if not user:
                user = await get_or_create_user(user_id)
            asyncio.get_event_loop().create_task(_delete_msg(user_id, event.message_id))   # drop the join message
            await _start_flow(event, user_id, user or {})
        else:
            await event.answer("❌ You haven't joined yet!", alert=True)

    # ── TERMS & CONDITIONS ───────────────────────────────────────
    elif data == "show_terms":
        terms_text = await get_setting("terms_text") or DEFAULT_TERMS_TEXT
        await event.edit(
            fancy_caps(terms_text),
            buttons=[[color_btn("🏠 Home", "main_menu", "default")]]
        )

    elif data == "terms_accept":
        await users_col.update_one({"user_id": user_id}, {"$set": {"accepted_terms": True, "accepted_terms_at": datetime.utcnow()}})
        await event.answer("✅ Terms accepted!")
        try:
            await event.delete()          # remove the old T&C message
        except Exception:
            pass
        await _send_main_welcome(event, user_id)

    elif data == "terms_decline":
        await event.edit(
            fancy_caps("❌ You must accept the terms to use this bot.\n\nsend /start to try again."),
        )

    # ── STORE (server select) ───────────────────────────────────
    elif data == "store":
        user_states.pop(user_id, None)
        server_count = int(await get_setting("server_count", 2))
        active_list = [i for i in range(1, server_count + 1) if await _server_active(i)]
        if len(active_list) == 1 and await get_setting("skip_server_step_if_one", False):
            user_states[user_id] = {"server": active_list[0]}
            await _enter_server(event, user_id, active_list[0])
            return
        per_row = 2
        rows, row, blocks = [], [], []
        for i in range(1, server_count + 1):
            active = await _server_active(i)
            info = await _server_label(i)
            dot = "🟢" if active else "🔴"
            style = "default"
            row.append(plain_btn(fancy_btn(f"Server {i}"), f"server:{i}"))
            if len(row) == per_row:
                rows.append(row)
                row = []
            tag = info.get("tag", "")
            short = " • ".join(info.get("bullets", [])[:2])
            status = " (Not Active Yet)" if not active else ""
            blocks.append(f"{dot} **Server {i}** — {tag}{status}\n{short}")
        if row:
            rows.append(row)
        rows.append([blue_btn(fancy_btn("Home"), "main_menu")])
        await event.edit(
            plain("🖥️ **Select a server**\n\n" + "\n\n".join(blocks)
                  + "\n\n👇 Tap a server below to continue."),
            buttons=rows
        )

    elif data.startswith("server:"):
        server_num = int(data.split(":", 1)[1])
        if not await _server_active(server_num):
            await event.answer(f"⚠️ Server {server_num} isn't activated right now — please try Server 1.", alert=True)
            return
        user_states[user_id] = {"server": server_num}
        await _enter_server(event, user_id, server_num)

    elif data.startswith("vnh_page:"):
        page = int(data.split(":", 1)[1])
        await _send_vnh_country_list(event, user_id, page, user_states.get(user_id, {}).get("vnh_search"))

    elif data == "vnh_search":
        _old = user_states.get(user_id, {})
        user_states[user_id] = {"state": "vnh_search", "server": _old.get("server", 2),
                                "vnh_search": _old.get("vnh_search"), "vnh_page": _old.get("vnh_page", 0)}
        _arm_prompt(user_id, event)
        await event.edit(fancy("🔍 **Send the country name to search:**"),
                          buttons=[[color_btn("❌ Cancel", f"vnh_page:{_old.get('vnh_page', 0)}", "default")]])

    elif data.startswith("vnh_country:"):
        code = data.split(":", 1)[1]
        await event.answer("⏳ Fetching live price…")
        result = await vnh_server.get_country_live_price(code)
        if not result.get("success"):
            await event.answer(f"❌ {result.get('message', 'Could not fetch live price.')}", alert=True)
            return
        if not user:
            user = await get_or_create_user(user_id)
        price = result["retail_inr"]
        bal = float(user.get("balance", 0))
        _old = user_states.get(user_id, {})
        _bk = f"vnh_page:{_old.get('vnh_page', 0)}"
        user_states[user_id] = {
            "server": int(await get_setting("vnh_server_number", 2)),
            "vnh_code": code, "vnh_price": price,
            "vnh_search": _old.get("vnh_search"), "vnh_page": _old.get("vnh_page", 0),
        }
        if bal < price:
            await event.edit(
                plain(f"⚠️ **Insufficient funds**\n\n💰 Price: **₹{price:.2f}**\n👛 Your balance: **₹{bal:.2f}**\n\n"
                      "Please add funds to continue with this purchase."),
                buttons=[
                    [green_btn("💳 Add funds", "deposit")],
                    [plain_btn(fancy_btn("Back"), _bk)],
                ]
            )
            return
        await event.edit(
            plain(f"⚡ **Confirm purchase**\n\n🌍 Country code: `{code}`\n💰 Price: **₹{price:.2f}**\n👛 Your balance: **₹{bal:.2f}**"),
            buttons=[
                [green_btn(f"✅ Buy · ₹{price:.2f}", f"vnh_buy:{code}")],
                [plain_btn("❌ Cancel", _bk)],
            ]
        )

    elif data.startswith("vnh_buy:"):
        code = data.split(":", 1)[1]
        st = user_states.get(user_id, {})
        price = st.get("vnh_price")
        if not price or st.get("vnh_code") != code:
            await event.answer("❌ Session expired — select the country again.", alert=True)
            return
        if not user:
            user = await get_or_create_user(user_id)
        bal = float(user.get("balance", 0))
        if bal < price:
            await event.answer("❌ Insufficient balance!", alert=True)
            return

        result = await users_col.update_one(
            {"user_id": user_id, "balance": {"$gte": price}},
            {"$inc": {"balance": -price}}
        )
        if result.modified_count == 0:
            await event.answer("❌ Insufficient balance!", alert=True)
            return

        order_result = await vnh_server.place_order(code)
        if not vnh_server.ok(order_result):
            # Never show raw supplier/provider errors to the customer.
            log.error(f"[VNH] order failed user={user_id} code={code} response={order_result!r}")
            await users_col.update_one({"user_id": user_id}, {"$inc": {"balance": price}})
            await event.edit(
                fancy(f"❌ **Something went wrong. please contact Admin.**\n\n`₹{price:.2f}` has been returned to your balance."),
                buttons=[[color_btn("◀️ Back", "store", "default")]]
            )
            await log_event(f"⚠️ **VNH order failed**\n• User: `{user_id}` • Code: `{code}`\n• Response: `{str(order_result)[:200]}`")
            return

        odata = order_result.get("data", order_result) if isinstance(order_result, dict) else {}
        number = _vnh_fetch_value(odata, "number", "phone", "phone_number")
        if not number:
            await users_col.update_one({"user_id": user_id}, {"$inc": {"balance": price}})
            await event.edit(
                fancy("❌ **Supplier didn't return a number.** you have been refunded."),
                buttons=[[color_btn("◀️ Back", "store", "default")]]
            )
            return

        await orders_col.insert_one({
            "user_id": user_id, "phone": number, "country_code": code,
            "amount": price, "source": "vnh", "status": "waiting_otp",
            "created_at": datetime.utcnow(),
        })
        user_states.pop(user_id, None)
        await event.edit(
            fancy("✅ **Purchase Successful!**\n\n")
            + fancy_line("number: ") + f"`{number}`\n\n"
            + fancy_line("tap below to fetch the otp — it may take a few seconds."),
            buttons=[
                [color_btn("📩 Get OTP", f"vnh_otp:{number}", "default")],
                [color_btn("🏠 Home", "main_menu", "default")],
            ]
        )
        await log_event(f"🛒 **VNH Purchase**\n• User: `{user_id}`\n• {code} — `₹{price:.2f}`\n• Number: `{number}`")

    elif data.startswith("vnh_otp:"):
        number = data.split(":", 1)[1]
        result = await vnh_server.get_code(number)
        if not vnh_server.ok(result):
            await event.answer("⏳ OTP not received yet — try again in a few seconds.", alert=True)
            return
        odata = result.get("data", result) if isinstance(result, dict) else {}
        otp = _vnh_fetch_value(odata, "code", "otp", "otp_code")
        pwd = _vnh_fetch_value(odata, "password", "2fa", "twofa")
        if not otp:
            await event.answer("⏳ OTP not received yet — try again in a few seconds.", alert=True)
            return
        msg = fancy("✅ **OTP Received!**\n\n") + fancy_line("code: ") + f"`{otp}`\n"
        if pwd:
            msg += fancy_line("2fa password: ") + f"`{pwd}`\n"
        await event.edit(msg, buttons=[
            [color_btn("🔄 Refresh", f"vnh_otp:{number}", "default")],
            [color_btn("🏠 Home", "main_menu", "default")],
        ])

    elif data.startswith("category:"):
        cat_name = data.split(":", 1)[1]
        prev_server = user_states.get(user_id, {}).get("server", 1)
        user_states[user_id] = {"category": cat_name, "server": prev_server}   # also clears any old search
        year_cfg = await _server_year_cfg(prev_server)
        if year_cfg["enabled"] or await _cat_has_year(cat_name):
            per_row = await _per_row()
            rows, row = [], []
            _srvq = ({"$or": [{"server": 1}, {"server": {"$exists": False}}]} if prev_server == 1 else {"server": prev_server})
            for y in year_cfg["years"] + ["none"]:
                _yq = {"$in": [None, ""]} if y == "none" else y
                n = await accounts_col.count_documents({"category": cat_name, "year": _yq, "status": "available", **_srvq})
                if n <= 0:
                    continue
                row.append(plain_btn(f"📅 {'Other' if y == 'none' else y} ({n})", f"year:{y}"))
                if len(row) == per_row:
                    rows.append(row)
                    row = []
            if row:
                rows.append(row)
            rows.append([plain_btn(fancy_btn("Back"), f"server:{prev_server}"), plain_btn(fancy_btn("Home"), "main_menu")])
            await event.edit(
                plain(
                    f"📅 **Select year** · {cat_name}\n\n"
                    "✨ Choose the account year you want.\n\n"
                    + ("👇 Tap a year below:" if len(rows) > 1 else "😔 No stock available right now.")
                ),
                buttons=rows
            )
            return
        await _send_country_list(event, user_id)

    elif data.startswith("year:"):
        st = user_states.get(user_id)
        if not st or "category" not in st:
            await event.answer("❌ Session expired. Start again.", alert=True)
            return
        st["year"] = data.split(":", 1)[1]
        await _send_country_list(event, user_id)

    elif data.startswith("store_page:"):
        page = int(data.split(":")[1])
        if not user_states.get(user_id, {}).get("category"):
            await event.answer("❌ Session expired. Start again.", alert=True)
            return
        user_states[user_id].pop("state", None)
        await _send_country_list(event, user_id, page)

    elif data == "store_noop":
        await event.answer()

    elif data == "cf" or data.startswith("cf_set:"):
        st = user_states.get(user_id) or {}
        if not st.get("category"):
            await event.answer("❌ Session expired. Start again.", alert=True)
            return
        if data.startswith("cf_set:"):
            st["min_stock"] = int(data.split(":")[1])
            await _send_country_list(event, user_id, 0)
            return
        cur = int(st.get("min_stock", 0) or 0)
        opts = [(0, "All"), (10, "10+"), (100, "100+"), (1000, "1000+")]
        await event.edit(
            plain("⚙️ **Filters**\n\nShow only countries with at least this much stock:"),
            buttons=[[styled_btn(("✅ " if cur == n else "") + lab + " in stock" if n else ("✅ " if cur == 0 else "") + "All countries",
                                 f"cf_set:{n}", STYLE_BLUE)] for n, lab in opts]
                    + [[styled_btn("← " + fancy_btn("Back"), "store_page:0", STYLE_GREEN)]])

    elif data == "store_sort":
        st = user_states.get(user_id) or {}
        if not st.get("category"):
            await event.answer("❌ Session expired. Start again.", alert=True)
            return
        st["sort"] = "desc" if st.get("sort", "asc") == "asc" else "asc"
        await _send_country_list(event, user_id, 0)

    elif data == "store_search":
        st = user_states.get(user_id) or {}
        if not st.get("category"):
            await event.answer("❌ Session expired. Start again.", alert=True)
            return
        st["state"] = "store_search"
        user_states[user_id] = st
        _arm_prompt(user_id, event)
        await event.edit(fancy("🔍 **Send the country name to search:**"),
                          buttons=[[color_btn("❌ Cancel", "store_page:0", "default")]])

    # ── ITEM DETAIL ──────────────────────────────────────────────
    elif data.startswith("detail:"):
        code = data.split(":")[1]
        c = await countries_col.find_one({"code": code})
        if not c:
            await event.answer("❌ Country not found.", alert=True)
            return
        cat_name = user_states.get(user_id, {}).get("category")
        stock = await accounts_col.count_documents(_stock_query(code, cat_name, user_states.get(user_id, {}).get("year")))
        # Step 3: Credit system (cr)
        text = plain(
            f"🌍 **{c['flag']} {c['name']}**\n\n"
            f"📦 Stock: **{stock}**\n"
            f"💰 Price: **₹{c['price']}**\n"
            f"🗂️ Category: **{cat_name or 'General'}**\n\n"
            "Purchase using the buy button below."
        )
        rows = [[green_btn("🛒 Buy now", f"buy:{code}"), plain_btn(fancy_btn("Back"), "store")]]
        if stock >= 2:
            rows.append([plain_btn("📦 Bulk buy", f"bulk_setup:{code}")])
        rows.append([plain_btn(fancy_btn("Home"), "main_menu")])
        await event.edit(text, buttons=rows)

    # ── BUY ──────────────────────────────────────────────────────
    elif data.startswith("buy:") or data.startswith("accpg:"):
        parts_ = data.split(":")
        code = parts_[1]
        page_ = int(parts_[2]) if data.startswith("accpg:") and len(parts_) > 2 else 0
        st_ = user_states.get(user_id, {})
        if st_.get("server", 1) != 1:
            await event.answer("⚠️ Yeh server abhi connect nahi hua — jald aa raha hai!", alert=True)
            return
        country = await countries_col.find_one({"code": code, "is_active": True})
        if not country:
            await event.answer("❌ Country unavailable.", alert=True)
            return
        cat_name, year_ = st_.get("category"), st_.get("year")
        q_ = _stock_query(code, cat_name, year_)
        total_ = await accounts_col.count_documents(q_)
        if total_ == 0:
            await event.answer("❌ Out of stock!", alert=True)
            return
        per_ = 16
        pages_ = (total_ - 1) // per_ + 1
        page_ = max(0, min(page_, pages_ - 1))
        order_ = int(st_.get("acc_order", 1))
        docs_ = await accounts_col.find(q_, {"_id": 1}).sort("_id", order_).skip(page_ * per_).limit(per_).to_list(per_)
        price_ = float(await get_cat_price(code, cat_name, country["price"]))
        fl_ = country.get("flag", "")
        _d = str(country.get("dial") or "").lstrip("+").strip()
        lab_ = f"{_fl(fl_)}{code}{'+' + _d if _d else ''} ¦ ₹{price_:g}"
        rows = []
        for i_ in range(0, len(docs_), 2):
            rows.append([blue_btn(lab_, f"buyacc:{code}:{d['_id']}") for d in docs_[i_:i_ + 2]])
        if pages_ > 1:
            rows.append(_page_row(page_, pages_, lambda i: f"accpg:{code}:{i}", f"accpg:{code}:{page_}", style="danger"))
        if total_ >= 2:
            rows.append([styled_btn(fancy_btn("Bulk Buy"), f"bulk_setup:{code}", STYLE_GREEN)])
        rows.append([styled_btn("← " + fancy_btn("Back"), f"store_page:{st_.get('list_page', 0)}", STYLE_GREEN),
                     styled_btn(fancy_btn("Filters"), f"acf:{code}", STYLE_GREEN)])
        await event.edit(
            RAW + f"{fl_}  **{country['name'].upper()}**\n{LINE}\n"
                  f"> Stock  :  **{total_:,}**\n> From   :  **₹{price_:g}**\n> Page   :  **{page_ + 1} of {pages_}**",
            buttons=rows)

    elif data.startswith("acf:") or data.startswith("accord:"):
        parts_ = data.split(":")
        code = parts_[1]
        st_ = user_states.setdefault(user_id, {})
        if data.startswith("accord:"):
            st_["acc_order"] = int(parts_[2])
            await event.answer("✅ Applied")
        cur_ = int(st_.get("acc_order", 1))
        await event.edit(
            plain("⚙️ **Filters**\n\nChoose how the accounts are listed:"),
            buttons=[[styled_btn(("✅ " if cur_ == 1 else "") + "Oldest first", f"accord:{code}:1", STYLE_BLUE),
                      styled_btn(("✅ " if cur_ == -1 else "") + "Newest first", f"accord:{code}:-1", STYLE_BLUE)],
                     [styled_btn("← Back", f"accpg:{code}:0", STYLE_GREEN)]])

    elif data.startswith("buyacc:"):
        _, code, oid_s = data.split(":", 2)
        server_num = user_states.get(user_id, {}).get("server", 1)
        if server_num != 1:
            await event.answer("⚠️ Yeh server abhi connect nahi hua — jald aa raha hai!", alert=True)
            return
        country = await countries_col.find_one({"code": code, "is_active": True})
        if not country:
            await event.answer("❌ Country unavailable.", alert=True)
            return
        cat_name = user_states.get(user_id, {}).get("category")
        acc_ = await accounts_col.find_one({"_id": _ObjId(oid_s), "status": "available"}, {"phone": 1})
        if not acc_:
            await event.answer("❌ That account was just sold. Pick another.", alert=True)
            return
        if not user:
            user = await get_or_create_user(user_id)
        bal = float(user.get("balance", 0))
        price = float(await get_cat_price(code, cat_name, country["price"]))  # Credits (per category)
        
        # Step 4: Insufficient Funds
        if bal < price:
            needed = price - bal
            text = plain(
                f"⚠️ **Insufficient funds**\n\n"
                f"🌍 Account: {country['flag']} {country['name']} · `{mask_public_phone(acc_['phone'])}`\n"
                f"💰 Price: **₹{price:g}**\n"
                f"👛 Your balance: **₹{bal:g}**\n"
                f"➖ Short by: **₹{needed:g}**\n\n"
                "Please add funds to proceed with this purchase."
            )
            await event.edit(text, buttons=[
                [green_btn("💳 Add funds", "deposit")],
                [plain_btn(fancy_btn("Back"), f"buy:{code}"), plain_btn(fancy_btn("Home"), "main_menu")]
            ])
            return
        
        # Confirm purchase (Step 4: Big Buy Button)
        text = plain(
            f"⚡ **Confirm purchase**\n\n"
            f"🌍 Country: **{country['flag']} {country['name']}**\n"
            f"📞 Account: `{mask_public_phone(acc_['phone'])}`\n"
            f"💰 Price: **₹{price:g}**\n"
            f"👛 Your balance: **₹{bal:g}**"
        )
        await event.edit(text, buttons=[
            [green_btn(f"✅ Buy this account · ₹{price:g}", f"confirm_buy:{code}:{oid_s}")],
            [plain_btn("❌ Cancel", f"buy:{code}"), plain_btn(fancy_btn("Home"), "main_menu")]
        ])

    # ── CONFIRM BUY ──────────────────────────────────────────────
    elif data.startswith("confirm_buy:"):
        _cb_parts = data.split(":")
        country_code = _cb_parts[1]
        acc_oid = _ObjId(_cb_parts[2]) if len(_cb_parts) > 2 else None
        country = await countries_col.find_one({"code": country_code, "is_active": True})
        if not country:
            await event.answer("❌ Country no longer available.", alert=True)
            return
        if not user:
            user = await get_or_create_user(user_id)
        price = float(await get_cat_price(country_code, user_states.get(user_id, {}).get("category"), country["price"]))  # Credits
        bal = float(user.get("balance", 0))
        if bal < price:
            await event.answer("❌ Insufficient balance!", alert=True)
            return
        st_ = user_states.get(user_id, {})
        cat_name = st_.get("category")

        # 1) take the money first, atomically (never sell on a stale balance)
        old_w = float(user.get("withdrawable", 0) or 0)
        w_ded = min(old_w, price)
        paid = await users_col.update_one(
            {"user_id": user_id, "balance": {"$gte": price}},
            {"$inc": {"balance": -price}, "$set": {"withdrawable": max(0.0, old_w - price)}})
        if not paid.modified_count:
            await event.answer("❌ Insufficient balance!", alert=True)
            return
        # 2) claim one account; 72h OTP window starts now
        session_doc = await accounts_col.find_one_and_update(
            ({"_id": acc_oid, "status": "available"} if acc_oid else _stock_query(country_code, cat_name, st_.get("year"))),
            {"$set": {"status": "sold", "buyer_id": user_id, **_sold_fields()}},
            sort=[("_id", 1)],
        )
        if not session_doc:
            await users_col.update_one({"user_id": user_id}, {"$inc": {"balance": price, "withdrawable": w_ded}})
            await event.answer("❌ Just sold to someone else — money refunded. Pick another account.", alert=True)
            return

        phone = session_doc["phone"]
        twofa = session_doc.get("twofa_password", "")
        await orders_col.insert_one({
            "user_id":      user_id,
            "phone":        phone,
            "country":      country["name"],
            "country_code": country_code,
            "country_flag": country.get("flag", ""),
            "amount":       price,
            "twofa":        twofa,
            "category":     cat_name,
            "status":       "waiting_otp",
            "created_at":   datetime.utcnow(),
        })
        pending_otp_requests[(user_id, phone)] = True
        await log_event(f"🛒 **Purchase**\n• User: `{user_id}`\n• {country.get('flag','')} {country['name']} — `₹{price}`\n• Phone: `{phone}`")

        # Step 4/7: Purchase success + OTP Request
        _ac_cache.clear()                     # stock just changed — next list is fresh
        msg = plain(
            f"✅ **Purchase successful!**\n\n"
            f"🌍 Country: **{country.get('flag','')} {country['name']}**\n"
            f"📞 Phone: `{phone}`\n"
            f"📂 Category: **{cat_name}**\n"
            f"🔐 2FA: `{twofa}`\n\n"
            "⏳ Tap **Request OTP** below to get your code."
        )
        await event.edit(msg, buttons=[
            [green_btn("📩 Request OTP", f"resend_{phone}")],
            [plain_btn(fancy_btn("Home"), "main_menu")]
        ])
        await public_log_event(
            "🛒 **New Purchase**\n"
            "• Server: `Server 1`\n"
            f"• User ID: `{mask_user_id(user_id)}`\n"
            f"• Country: {country.get('flag','')} {country['name']}\n"
            f"• Number: `{mask_public_phone(phone)}`\n"
            f"• Amount: `₹{price}`\n"
            f"• {now_ist().strftime('%d/%m/%Y %H:%M:%S')} IST\n\n"
            "💙 Thank you for your purchase!")

    # ── REQUEST OTP ─────────────────────────────────────────────
    elif data.startswith("resend_"):
        phone = data[7:]
        await event.answer("⏳ Requesting OTP…", alert=False)
        pending_otp_requests[(user_id, phone)] = True   # re-arm — otherwise the next OTP is silently dropped
        success = await acc_mgr.request_otp(phone)
        if not success:
            pending_otp_requests.pop((user_id, phone), None)
        if success:
            _track_temp(user_id, await event.respond(f"📤 OTP request sent for `{phone}`."))
        else:
            _track_temp(user_id, await event.respond(f"❌ Could not trigger OTP for `{phone}`."))

    # ── LOGOUT ──────────────────────────────────────────────────
    elif data.startswith("logout_"):
        phone = data[7:]
        await acc_mgr.logout_client(phone)
        await accounts_col.find_one_and_update(
            {"phone": phone, "status": "sold"},
            {"$set": {"status": "logged_out", "logged_out_at": datetime.utcnow()}},
            sort=[("sold_at", -1)],
        )
        await event.answer("✅ Logged out.", alert=False)
        await event.edit(
            fancy(f"🔓 **Logged out**\n\n`{phone}` has been disconnected."),
            buttons=[[color_btn("🏠 Home", "main_menu", "default")]],
        )

    # ── MY ORDERS ──────────────────────────────────────────────
    elif data == "orders":
        docs = await orders_col.find(
            {"user_id": user_id}
        ).sort("created_at", -1).limit(8).to_list(8)
        if not docs:
            await event.edit(
                fancy("📋 **My orders**\n\n_no orders yet._"),
                buttons=[[color_btn("🛒 Buy Now", "store", "default"),
                          color_btn("🏠 Home", "main_menu", "default")]],
            )
            return
        _STATUS = {
            "waiting_otp": "⏳ Waiting OTP",
            "completed":   "✅ Completed",
            "cancelled":   "❌ Cancelled",
            "logged_out":  "🔓 Logged Out",
        }
        lines = [fancy("📋 **My Orders — Last 8**\n")]
        for i, o in enumerate(docs, 1):
            st = _STATUS.get(o.get("status", ""), o.get("status", "").title())
            line = (
                f"**{i}.** {o.get('country_flag','')} **{o.get('country','?')}**  —  {st}\n"
                f"📱 `{o.get('phone','?')}`  •  ₹{o.get('amount',0):.0f}"
            )
            if o.get("twofa"):
                line += f"\n🔐 2FA: `{o['twofa']}`"
            lines.append(line)
        kb = [[color_btn("🏠 Home", "main_menu", "default")]]
        if docs[0].get("status") == "waiting_otp":
            kb.insert(0, [color_btn("📩 Re-Request OTP", f"resend_{docs[0]['phone']}", "default")])
        await event.edit("\n\n".join(lines), buttons=kb)

    # ── HISTORY ──────────────────────────────────────────────────
    elif data == "history":
        orders = await orders_col.find(
            {"user_id": user_id}).sort("created_at", -1).limit(6).to_list(6)
        deps   = await deposits_col.find(
            {"user_id": user_id}).sort("created_at", -1).limit(5).to_list(5)
        spent   = sum(float(o.get("amount", 0)) for o in orders
                      if o.get("status") != "cancelled")
        dep_tot = sum(float(d.get("amount", 0)) for d in deps
                      if d.get("status") == "approved")
        lines = [
            fancy("📋 **Transactions**\n"),
            f"💸 Total Spent:     `₹{spent:.2f}`",
            f"💰 Total Deposited: `₹{dep_tot:.2f}`",
        ]
        if orders:
            lines.append("\n🛒 **Recent Purchases:**")
            for o in orders:
                lines.append(
                    f"• {o.get('country_flag','')} {o.get('country','?')}"
                    f" — `₹{o.get('amount',0):.0f}` — `{o.get('phone','?')}`"
                )
        if deps:
            lines.append("\n💰 **Recent Deposits:**")
            _DE = {"approved": "✅", "pending": "⏳", "rejected": "❌"}
            for d in deps:
                lines.append(
                    f"{_DE.get(d.get('status',''),'•')} "
                    f"₹{d.get('amount',0):.0f} — {d.get('status','').title()}"
                )
        await event.edit(
            "\n".join(lines),
            buttons=[[color_btn("Back", "balance", "success")]],
        )

    # ─── ADD FUNDS (deposit method) ──────────────────────────────
    elif data == "deposit":
        user_states.pop(user_id, None)
        btns = []
        if RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET:
            btns.append([color_btn("UPI · Automatic", "dep_upi:auto", "primary")])
        elif await get_setting("upi_id"):          # Razorpay not set up: manual is the only option
            btns.append([color_btn("UPI · Manual", "dep_upi:manual", "primary")])
        else:
            btns.append([color_btn("UPI · Automatic", "dep_upi:auto", "primary")])
        btns.append([color_btn("Deposit Packages", "deposit_pkgs", "primary")])
        btns.append([color_btn("Back", "balance", "success")])
        await event.edit(
            RAW + "**ADD FUNDS**\n\n"
            f"{LINE}\n"
            "Select a deposit method:\n"
            f"{LINE}",
            buttons=btns,
        )

    elif data.startswith("dep_upi:"):
        method = data.split(":", 1)[1]
        min_d, max_d = await _deposit_limits()
        user_states[user_id] = {"state": "custom_deposit", "prompt_id": event.message_id, "method": method}
        title = "UPI · AUTOMATIC" if method == "auto" else "UPI · MANUAL"
        await event.edit(
            RAW + f"**{title}**\n\n"
            "Enter the amount you want to deposit (₹):\n\n"
            f"Minimum : ₹{min_d:g}\n"
            f"Maximum : ₹{max_d:g}\n"
            "",
            buttons=[[color_btn("Cancel", "dep_cancel", "danger")]],
        )

    elif data == "dep_cancel":
        user_states.pop(user_id, None)
        await event.edit("Deposit cancelled.",
                         buttons=[[color_btn("Back to Wallet", "balance", "success")]])

    elif data == "deposit_pkgs":
        pkgs = []
        async for p in packages_col.find({}).sort("credits", 1):
            pkgs.append(p)
        if not user:
            user = await get_or_create_user(user_id)
        current_balance = float(user.get("balance", 0))
        withdrawable_balance = float(user.get("withdrawable", 0))
        rows = []
        for i in range(0, len(pkgs), 2):
            rows.append([color_btn(f"₹{p['credits']}", f"pkg:{p['credits']}", "primary")
                         for p in pkgs[i:i+2]])
        rows.append([color_btn("Custom Amount", "custom_deposit", "primary")])
        rows.append([color_btn("Support", "help", "primary")])
        rows.append([color_btn("Back", "deposit", "success")])
        await event.edit(
            RAW + "**DEPOSIT PACKAGES**\n\n"
            f"{LINE}\n"
            f"Balance      : **₹{current_balance:.2f}**\n"
            f"Withdrawable : ₹{withdrawable_balance:.2f}\n"
            f"{LINE}\n\n"
            "__Select a deposit package below:__",
            buttons=rows,
        )

    elif data.startswith("pkg:"):
        credits = int(data.split(":")[1])
        pkg = await packages_col.find_one({"credits": credits})
        if not pkg:
            await event.answer("❌ Package not found.", alert=True)
            return
        user_states[user_id] = {"deposit_pkg": credits, "pkg_data": pkg}
        if RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET:      # automatic only — go straight to the QR
            await _start_razorpay_auto_deposit(event, user_id, pkg["price"], credits)
            return
        methods = [
            [color_btn("UPI · Manual", f"pay_method:manual:{credits}", "primary")],
            [color_btn("Back", "deposit_pkgs", "success")]
        ]
        await event.edit(
            RAW + "**SELECT PAYMENT METHOD**\n\n"
            f"{LINE}\n"
            f"Package : **₹{credits}**\n"
            f"{LINE}\n\n"
            "__UPI · Manual — pay, send the screenshot, admin approves.__",
            buttons=methods
        )

    elif data.startswith("pay_method:"):
        _, method, credits_str = data.split(":")
        credits = int(credits_str)
        pkg = await packages_col.find_one({"credits": credits})
        if not pkg:
            await event.answer("❌ Package error.", alert=True)
            return
        amount = pkg["price"]

        if method == "auto":
            await _start_razorpay_auto_deposit(event, user_id, amount, credits)

        elif method == "manual":
            await _start_manual_deposit(event, user_id, amount, credits)

    elif data == "upi_app":
        st = user_states.get(user_id, {})
        upi_id = await get_setting("upi_id")
        amount = st.get("amount")
        if st.get("state") == "await_deposit_screenshot" and upi_id and amount:
            note = (f"📲 **Pay in your UPI app**\n\nopen any UPI app → send money → UPI ID:\n`{upi_id}`\n"
                    f"Amount: `₹{float(amount):.2f}`\n\nthen send the screenshot here.")
        else:
            note = ("📲 **Pay in your UPI app**\n\nsave the QR image sent above, open any UPI app → "
                    "Scan & pay → choose the QR from gallery.")
        _track_temp(user_id, await event.respond(fancy(note)))
        await event.answer()

    elif data == "cancel_payment":
        user_states.pop(user_id, None)
        dep = await deposits_col.find_one({"user_id": user_id, "status": "pending"}, sort=[("_id", -1)])
        if dep:
            await deposits_col.update_one({"_id": dep["_id"]}, {"$set": {"status": "cancelled"}})
            await ext_close_deposit_source(dep)
        # The Cancel button sits on the QR *photo* message — editing it would only
        # change the caption and leave the QR image behind, so delete it instead.
        try:
            await event.delete()
        except Exception:
            pass
        await bot.send_message(
            user_id,
            "Deposit cancelled.",
            buttons=[[color_btn("Back to Wallet", "balance", "success")]]
        )

    elif data.startswith("pay_method_custom:"):
        method = data.split(":", 1)[1]
        state = user_states.get(user_id, {})
        amount = state.get("custom_amount")
        credits = state.get("custom_credits")
        if amount is None or credits is None:
            await event.answer("❌ No active custom deposit. Start again.", alert=True)
            return
        if method == "auto":
            await _start_razorpay_auto_deposit(event, user_id, amount, credits)
        else:
            await _start_manual_deposit(event, user_id, amount, credits)

    elif data in ("check_payment", "deposit_paid"):
        await _verify_deposit_ui(event, user_id)


    elif data == "custom_deposit":
        user_states[user_id] = {"state": "custom_deposit", "prompt_id": event.message_id}
        min_d, max_d = await _deposit_limits()
        await event.edit(
            RAW + "**CUSTOM AMOUNT**\n\n"
            "Enter the amount you want to deposit (₹):\n\n"
            f"Minimum : ₹{min_d:g}\n"
            f"Maximum : ₹{max_d:g}\n"
            "",
            buttons=[[color_btn("Back", "deposit_pkgs", "success")]]
        )

    # ── PROFILE ──────────────────────────────────────────────────
    elif data == "profile":
        if not user:
            user = await get_or_create_user(user_id)
        sender = await event.get_sender()
        full_name = " ".join(x for x in [getattr(sender, "first_name", None), getattr(sender, "last_name", None)] if x)
        name = _clean_md(full_name) or "User"
        uname = getattr(sender, "username", None)
        uname_txt = f"@{uname}" if uname else "Not set"
        joined = user.get("joined_at")
        joined_txt = (joined + timedelta(hours=5, minutes=30)).strftime("%d %b %Y") if joined else "N/A"
        bal = float(user.get("balance", 0))
        orders_count = await orders_col.count_documents({"user_id": user_id})
        await event.edit(
            RAW + "**PROFILE**\n\n"
            f"{LINE}\n"
            f"Name       : {name}\n"
            f"Username   : {uname_txt}\n"
            f"User ID    : {user_id}\n"
            f"Joined     : {joined_txt}\n"
            f"{LINE}\n"
            f"Balance    : **₹{bal:.2f}**\n"
            f"Orders     : {orders_count}\n"
            f"{LINE}",
            buttons=[[color_btn("Back", "main_menu", "success")]]
        )

    # ── LANGUAGE ──────────────────────────────────────────────────
    elif data == "language":
        langs = [
            ("🇬🇧 English", "en"), ("🇮🇳 हिन्दी", "hi"), ("🇷🇺 Русский", "ru"),
            ("🇹🇷 Türkçe", "tr"), ("🇮🇳 தமிழ்", "ta"), ("🇮🇳 മലയാളം", "ml"),
        ]
        rows = []
        for label, code in langs:
            rows.append([color_btn(label, f"set_lang:{code}", "default")])
        rows.append([color_btn("🏠 Home", "main_menu", "default")])
        await event.edit(
            fancy("🌐 **Language Settings**\n\nChoose your preferred language:"),
            buttons=rows
        )

    elif data.startswith("set_lang:"):
        lang_code = data.split(":")[1]
        await users_col.update_one({"user_id": user_id}, {"$set": {"language": lang_code}})
        await event.answer(f"✅ Language set to {lang_code}", alert=True)
        await callback_router(event, "profile")

    # ── REFERRAL ──────────────────────────────────────────────────
    elif data == "referral":
        if not user:
            user = await get_or_create_user(user_id)
        pct      = float(await get_setting("referral_percent", 0))
        bonus    = float(await get_setting("referral_bonus", 0))
        ref_code = user.get("referral_code", "")
        earnings = float(user.get("referral_earnings", 0))
        count    = await users_col.count_documents({"referred_by": user_id})
        uname    = await get_bot_username()
        ref_link = f"https://t.me/{uname}?start=ref_{ref_code}"
        await event.edit(
            fancy(
                f"🎁 **Refer & Earn**\n\n"
                f"Earn **{pct:.1f}%** on every deposit!\n"
                f"Plus **₹{bonus:.0f}** instant join bonus!\n\n"
                f"🔗 **Your Link:**\n`{ref_link}`\n\n"
                f"👥 Total Referred: **{count}**\n"
                f"💰 Total Earned: `₹{earnings:.2f}`"
            ),
            buttons=[
                [url_btn("Share Link", f"https://t.me/share/url?url={ref_link}&text=Buy+Telegram+accounts+instantly!", "success")],
                [color_btn("🏠 Home", "main_menu", "default")],
            ],
        )

    # ── HELP ─────────────────────────────────────────────────────
    elif data == "help":
        await event.edit(
            fancy("❓ **Help Center**\n\nChoose a topic below:"),
            buttons=[
                [color_btn("📖 How to Use", "help_howto", "default")],
                [color_btn("🔑 OTP Help", "help_otp", "default")],
                [color_btn("💳 Payment Help", "help_payment", "default")],
                [color_btn("🛡️ Why Trust Us?", "help_trust", "default")],
                [color_btn("📞 Contact Support", "support", "default")],
                [color_btn("🏠 Home", "main_menu", "default")]
            ]
        )

    elif data == "help_howto":
        await event.edit(
            fancy("📖 **How to Use**\n\n"
                  "1️⃣ Add credits via UPI / QR.\n"
                  "2️⃣ Go to store → select category.\n"
                  "3️⃣ Choose a country → tap buy.\n"
                  "4️⃣ Receive OTP & 2FA instantly.\n"
                  "5️⃣ Re-Request OTP within 24h."),
            buttons=[[color_btn("◀️ Back", "help", "default")]]
        )

    elif data == "help_otp":
        await event.edit(
            fancy("🔑 **OTP Troubleshooting**\n\n"
                  "⚠️ Code not arrived?\n→ request again.\n\n"
                  "❓ Where is 2FA?\n→ check order details."),
            buttons=[[color_btn("◀️ Back", "help", "default")]]
        )

    elif data == "help_payment":
        await event.edit(
            fancy("💳 **Payment Help**\n\n"
                  "| Method | Time |\n"
                  "⚡ UPI / QR auto-verify — credited in 1–2 min.\n"
                  "📸 UPI / QR manual — credited after Admin approval.\n\n"
                  "✔ Paid but credits not added?\n→ tap 'check payment' or contact support."),
            buttons=[[color_btn("◀️ Back", "help", "default")]]
        )

    elif data == "help_trust":
        await event.edit(
            fancy("🛡️ **Why trust OTP bot?**\n\n🔹 100% Automated\n🔹 Instant OTP Forwarding\n🔹 No human sees session data"),
            buttons=[[color_btn("◀️ Back", "help", "default")]]
        )

    elif data == "support":
        support_link = await get_setting("support_link")
        if support_link:
            await event.edit(fancy("📞 **Contact Support**\n\nTap below to chat."),
                buttons=[[url_btn("Support", _norm_link(support_link))], [color_btn("◀️ Back", "help", "default")]])
        else:
            await event.edit(fancy("📞 **Support**\n\nNo support link configured."),
                buttons=[[color_btn("◀️ Back", "help", "default")]])

    # ── WHATSAPP ──────────────────────────────────────────────────
    elif data == "whatsapp":
        await event.edit(
            fancy("💬 **WhatsApp**\n\nContact our whatsapp support for assistance."),
            buttons=[[color_btn("🏠 Home", "main_menu", "default")]]
        )

    # ════════════════════════════════════════════
    #  ADMIN CALLBACKS
    # ════════════════════════════════════════════
    elif data == "admin":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        owner_flag = (user_id == OWNER_ID)
        await event.edit(
            fancy("⚙️ **Admin panel**\n\nselect action:"),
            buttons=_admin_menu_buttons(owner_flag),
        )

    elif data == "astats":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        total_users  = await users_col.count_documents({})
        total_acc    = await accounts_col.count_documents({})
        avail_acc    = await accounts_col.count_documents({"status": "available"})
        total_orders = await orders_col.count_documents({})
        pending_deps = await deposits_col.count_documents({"status": "pending"})
        banned       = await users_col.count_documents({"is_banned": True})
        rev_pipe     = await deposits_col.aggregate([
            {"$match": {"status": "approved"}},
            {"$group": {"_id": None, "total": {"$sum": "$amount"}}},
        ]).to_list(1)
        revenue  = rev_pipe[0]["total"] if rev_pipe else 0
        today    = datetime.utcnow().replace(hour=0, minute=0, second=0, microsecond=0)
        new_today = await users_col.count_documents({"joined_at": {"$gte": today}})
        db_admins = await bot_admins_col.count_documents({"is_active": True})
        await event.edit(
            fancy(
                f"📊 **Bot Statistics**\n\n"
                f"👥 Total Users: `{total_users}` (+{new_today} Today)\n"
                f"🚫 Banned: `{banned}`\n"
                f"🔑 Extra Admins: `{db_admins}`\n\n"
                f"📦 Total Sessions: `{total_acc}`\n"
                f"✅ Available: `{avail_acc}`\n"
                f"🛒 Total Orders: `{total_orders}`\n\n"
                f"💳 Pending Deposits: `{pending_deps}`\n"
                f"💰 Total Revenue: `₹{revenue:.2f}`"
            ),
            buttons=[[color_btn("◀️ Back", "admin", "default")]],
        )

    elif data == "upload_sessions":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        server_count = int(await get_setting("server_count", 2))
        rows = []
        row = []
        for i in range(1, server_count + 1):
            row.append(color_btn(f"Server {i}", f"upload_srv:{i}", "default"))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([color_btn("◀️ Back", "admin", "default")])
        await event.edit(fancy("📦 **Upload Sessions**\n\nSelect which server this stock belongs to:"), buttons=rows)

    elif data.startswith("upload_srv:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        srv_n = data.split(":", 1)[1]
        cats = await get_categories()
        rows = []
        for cat in cats:
            rows.append([color_btn(f"{cat['icon']} {cat['name']}", f"upload_cat:{srv_n}:{cat['name']}", "default")])
        rows.append([color_btn("◀️ Back", "upload_sessions", "default")])
        note = "" if srv_n == "1" else "\n\n⚠️ Note: Servers Other Than 1 Aren'T Connected Yet — Stock Won'T be sold until that server is wired up."
        await event.edit(fancy(f"📦 **Upload to Server {srv_n}**\n\nselect category:" + note), buttons=rows)

    elif data.startswith("upload_cat:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        _, srv_n, cat_name = data.split(":", 2)
        c_list = await countries_col.find({"is_active": True}).to_list(300)
        prices = {d["code"]: d["price"] async for d in cat_prices_col.find({"category": cat_name})}
        rows, row = [], []
        for c in c_list:
            pr = prices.get(c["code"])
            tag = f" • {pr:g}" if pr is not None else ""
            row.append(color_btn(f"{c['flag']} {c['name']}{tag}", f"upload_country:{srv_n}:{c['code']}:{cat_name}", "default"))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([color_btn("➕ Add Country", f"upload_addcountry:{srv_n}:{cat_name}", "success")])
        rows.append([color_btn("◀️ Back", f"upload_srv:{srv_n}", "default")])
        await event.edit(fancy(f"📦 **Upload to {cat_name} (Server {srv_n})**\n\nSelect a country (price shown if already set):"), buttons=rows)

    elif data.startswith("upload_addcountry:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        _, srv_n, cat_name = data.split(":", 2)
        user_states[user_id] = {"state": "add_country_cat", "srv": srv_n, "cat": cat_name}
        await event.edit(
            fancy(f"🌍 **Add country to {cat_name}**\n\nSend just the country **name** or **code**.\nExamples: `Turkey` · `TR` · `United States`\n\nFlag and short code are filled automatically. If the country already exists it is reused — nothing to add twice."),
            buttons=[[color_btn("❌ Cancel", f"upload_cat:{srv_n}:{cat_name}", "default")]])

    elif data.startswith("upload_country:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        parts = data.split(":", 3)
        if len(parts) < 4:
            await event.answer("❌ Error.", alert=True)
            return
        _, srv_n, cc, cat_name = parts
        year_cfg = await _server_year_cfg(int(srv_n))
        if year_cfg["enabled"] or await _cat_has_year(cat_name):
            per_row = await _per_row()
            rows, row = [], []
            for y in year_cfg["years"]:
                row.append(color_btn(y, f"upload_year:{srv_n}:{cc}:{cat_name}:{y}", "default"))
                if len(row) == per_row:
                    rows.append(row)
                    row = []
            if row:
                rows.append(row)
            rows.append([color_btn("◀️ Back", f"upload_cat:{srv_n}:{cat_name}", "default")])
            await event.edit(fancy("📅 **Upload — select year**\n\nwhich year are these accounts from?"), buttons=rows)
            return
        await _price_gate(event, user_id, srv_n, cc, cat_name)

    elif data.startswith("upload_year:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        _, srv_n, cc, cat_name, yr = data.split(":", 4)
        await _price_gate(event, user_id, srv_n, cc, cat_name, yr)

    elif data == "cp_use":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        st = user_states.get(user_id) or {}
        if st.get("state") != "set_cat_price":
            await event.answer("❌ Expired. Start the upload again.", alert=True)
            return
        await set_cat_price(st["cc"], st["cat"], st["default"])
        user_states.pop(user_id, None)
        await _begin_upload(event, user_id, st["srv"], st["cc"], st["cat"], st.get("year"))

    elif data == "manage_sessions":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        total   = await accounts_col.count_documents({})
        avail   = await accounts_col.count_documents({"status": "available"})
        sold    = await accounts_col.count_documents({"status": "sold"})
        logout_ = await accounts_col.count_documents({"status": "logged_out"})
        pipe = await accounts_col.aggregate([
            {"$match": {"status": "available"}},
            {"$group": {"_id": "$country", "count": {"$sum": 1}, "flag": {"$first": "$country_flag"}}},
            {"$sort": {"count": -1}},
        ]).to_list(20)
        by_country = "\n".join(
            f"  {r.get('flag','🌍')} {r['_id']}: `{r['count']}`"
            for r in pipe
        ) or "  (Empty)"
        await event.edit(
            fancy(
                f"📋 **Session Overview**\n\n"
                f"Total: `{total}`\n"
                f"✅ Available: `{avail}`\n"
                f"🔑 Sold: `{sold}`\n"
                f"🔓 Logged Out: `{logout_}`\n\n"
                f"**Available by Country:**\n{by_country}"
            ),
            buttons=[[color_btn("◀️ Back", "admin", "default")]],
        )

    elif data == "pending_deposits":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        deps = await deposits_col.find({"status": "pending"}).sort("created_at", 1).limit(10).to_list(10)
        if not deps:
            await event.edit(fancy("✅ No Pending Deposits."),
                buttons=[[color_btn("◀️ Back", "admin", "default")]])
            return
        await event.answer()
        for dep in deps:
            from bson import ObjectId
            dep_id  = str(dep["_id"])
            uid     = dep["user_id"]
            amount  = dep["amount"]
            created = dep["created_at"].strftime("%d %b %H:%M")
            await bot.send_message(
                user_id,
                fancy(f"💳 **Deposit Request**\n• User ID: `{uid}`\n• Amount: `₹{amount:.2f}`\n• Time: {created}"),
                buttons=[
                    [color_btn("✅ Approve", f"dep_approve:{dep_id}:{uid}:{amount}", "default"),
                     color_btn("❌ Reject", f"dep_reject:{dep_id}:{uid}", "default")],
                ],
            )

    elif data.startswith("dep_approve:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        from bson import ObjectId
        _, dep_id, uid_str, amount_str = data.split(":", 3)
        uid    = int(uid_str)
        amount = float(amount_str)

        claim = await deposits_col.update_one(
            {"_id": ObjectId(dep_id), "status": "pending"},
            {"$set": {"status": "approved", "approved_at": datetime.utcnow(), "approved_by": user_id}},
        )
        if claim.matched_count == 0:
            await event.answer("⚠️ Already processed.", alert=True)
            return

        dep_doc = await deposits_col.find_one({"_id": ObjectId(dep_id)})
        if dep_doc:
            uid    = int(dep_doc.get("user_id", uid))
            amount = float(dep_doc.get("amount", amount))
            credits = dep_doc.get("credits", 0)

        await users_col.update_one({"user_id": uid}, {"$inc": {"balance": amount}})
        await referral_first_deposit_bonus(uid, amount)
        await sync_payment_group_message(dep_doc or {}, f"✅ **APPROVED** by `{user_id}`")
        try:
            await bot.send_message(uid, fancy(f"✅ **Deposit Approved!**\n`₹{amount:.2f}` Added to your wallet."))
        except Exception:
            pass
        await log_event(f"✅ **Manual Deposit Approved**\n• User: `{uid}`\n• ₹{amount:.2f} → +₹{dep_doc.get('credits', 0) if dep_doc else 0}\n• By Admin: `{user_id}`")
        await event.edit(f"✅ Approved ₹{amount:.2f} For User `{uid}`.")

    elif data.startswith("dep_reject:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        from bson import ObjectId
        _, dep_id, uid_str = data.split(":", 2)
        uid = int(uid_str)
        dep_doc = await deposits_col.find_one_and_update(
            {"_id": ObjectId(dep_id), "status": "pending"},
            {"$set": {"status": "rejected", "rejected_at": datetime.utcnow(), "rejected_by": user_id}},
            return_document=True,
        )
        if dep_doc is None:
            await event.answer("⚠️ Already processed.", alert=True)
            return
        uid = int(dep_doc.get("user_id", uid))
        try:
            await bot.send_message(uid, fancy("❌ **Deposit rejected.**\ncontact support."))
        except Exception:
            pass
        await event.edit(f"❌ Rejected deposit for user `{uid}`.")

    elif data == "broadcast":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        user_states[user_id] = {"state": "broadcast"}
        await event.edit(fancy("📢 **Broadcast**\n\nSend the message to broadcast to all users."),
            buttons=[[color_btn("❌ Cancel", "admin", "default")]])

    elif data == "asettings":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        upi    = await get_setting("upi_id",         "Not set")
        uname_ = await get_setting("upi_name",        "Prime Vault")
        sup    = await get_setting("support_link",    "Not set")
        bn     = await get_setting("bot_name",        "Prime Vault")
        rb     = await get_setting("referral_bonus",  0)
        rp     = await get_setting("referral_percent", 0)
        md     = await get_setting("min_deposit",     10)
        mxd    = await get_setting("max_deposit",     100000)
        sales_ = await get_setting("sales_link",      "Not set")
        wa     = "✅" if await get_setting("whatsapp_enabled") else "❌"
        photo  = "✅" if await get_setting("welcome_photo") else "❌"
        rzp    = "✅ Configured" if (RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET) else "❌ Not Set (.Env)"
        vnh_on = "✅ Connected" if vnh_server.configured else "❌ Not Set (.Env)"
        vnh_mk = await vnh_server.get_markup_percent()
        skip1  = "✅" if await get_setting("skip_server_step_if_one", False) else "❌"
        logs_ch = LOGS_CHANNEL_ID or await get_setting("logs_channel_id", 0)
        default2fa = await get_setting("default_2fa", "")
        srv_count = await get_setting("server_count", 2)
        server_count_ = int(await get_setting("server_count", 2))
        year_lines = []
        for i in range(1, server_count_ + 1):
            c_ = await _server_year_cfg(i)
            active_ = await _server_active(i)
            year_lines.append(f"Server {i}: {'🟢 On' if active_ else '🔴 Off'} • Year {'✅' if c_['enabled'] else '❌'} (`{', '.join(c_['years'])}`)")
        per_row_v = await _per_row()
        await event.edit(
            fancy(
                f"⚙️ **Settings**\n\n"
                f"• Bot Name: `{bn}`\n"
                f"• UPI ID: `{upi}`\n"
                f"• UPI Name: `{uname_}`\n"
                f"• Support: `{sup}`\n"
                f"• Referral: join `₹{await get_referral_signup_bonus()}` • first deposit `{await get_referral_bonus_percent()}%` (max `{await get_referral_bonus_max()}`) {'🟢' if await is_referral_enabled() else '🔴'}\n"
                f"• Server 3: {'✅ Connected' if server3_server.configured else '❌ Not Set (.Env)'} • Markup `{await server3_server.get_markup_percent()}%`\n"
                f"• Min Deposit: `₹{md}`\n"
                f"• Max Deposit: `₹{mxd}`\n"
                f"• WhatsApp: {wa}\n"
                f"• Welcome Photo: {photo}\n"
                f"• Razorpay Auto-Verify: {rzp}\n"
                f"• VNH Supplier (Server {await get_setting('vnh_server_number', 2)}): {vnh_on} • Markup `{vnh_mk}%`\n"
                f"• Skip 1-Server Step: {skip1}\n"
                f"• Logs Channel: `{logs_ch or 'Not Set'}`\n"
                f"• Default 2FA: `{default2fa or 'None'}`\n"
                f"• Servers: `{srv_count}`\n"
                + "\n".join(f"• {l}" for l in year_lines) + "\n"
                f"• Buttons Per Row: `{per_row_v}`"
            ),
            buttons=[
                [color_btn("🤖 Bot Name", "set_botname", "default"), color_btn("💳 UPI ID", "set_upi", "default")],
                [color_btn("👤 UPI Name", "set_upiname", "default"), color_btn("📞 Support", "set_support", "default")],
                [color_btn("🎁 Referral", "admin_referral_settings", "default"), color_btn("💳 Payment Control", "admin_payment_options", "default")],
                [color_btn("📢 Channels & Logs", "admin_channels", "default"), color_btn("🛡️ Force Join", "admin_force_join", "default")],
                [color_btn("🌐 Server 3", "admin_server3", "default")],
                [color_btn("🔢 Min Deposit", "set_min_dep", "default"), color_btn("🔢 Max Deposit", "set_max_dep", "default")],
                [color_btn("🖥️ Servers", "set_server_count", "default")],
                [color_btn("💬 Toggle WhatsApp", "toggle_whatsapp", "default"), color_btn("🖼️ Set Welcome Photo", "set_welcome_photo", "default")],
                [color_btn("📋 Logs Channel", "set_logs_channel", "default"), color_btn("🔐 Default 2FA", "set_default_2fa", "default")],
                [color_btn("🏷️ Server Labels", "set_server_labels", "default"), color_btn("🔌 Toggle Server", "set_toggle_server", "default")],
                [color_btn("📅 Year Settings", "set_year_cfg", "default")],
                [color_btn("🔲 Buttons/Row", "set_per_row", "default"), color_btn("📈 VNH Markup %", "set_vnh_markup", "default")],
                [color_btn("⏭️ Skip 1-Server Step", "toggle_skip_server", "default"), color_btn("🗑️ Remove UPI ID", "remove_upi", "default")],
                [color_btn("⭐ Vip Discount %", "set_vip_discount", "default")],
                [color_btn("◀️ Back", "admin", "default")],
            ],
        )

    elif data in (
        "set_botname", "set_upi", "set_upiname", "set_support",
        "set_ref_bonus", "set_ref_pct", "set_min_dep", "set_max_dep",
        "toggle_whatsapp", "set_welcome_photo",
        "set_default_2fa", "set_server_count", "set_logs_channel",
        "set_server_labels", "set_toggle_server", "set_year_cfg", "set_per_row", "set_vnh_markup",
        "toggle_skip_server", "remove_upi"
    ):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        _prompts = {
            "set_botname":      ("setting_botname",  "🤖 Send new bot name:"),
            "set_upi":          ("setting_upi",       "💳 Send new UPI ID:"),
            "set_upiname":      ("setting_upiname",   "👤 Send UPI display name:"),
            "set_support":      ("setting_support",   "📞 Send Support Link:"),
            "set_ref_bonus":    ("setting_ref_bonus", "🎁 Send referral join bonus (₹):"),
            "set_ref_pct":      ("setting_ref_pct",   "📈 Send Referral Deposit %:"),
            "set_min_dep":      ("setting_min_dep",   "🔢 Send Minimum Deposit (₹):"),
            "set_max_dep":      ("setting_max_dep",   "🔢 Send Maximum Deposit (₹):"),
            "toggle_whatsapp":  ("whatsapp_toggle",   None),
            "set_welcome_photo":("welcome_photo_set", "🖼️ Send the photo to use as welcome image."),
            "set_default_2fa":  ("setting_default_2fa", "🔐 Send default 2FA password:"),
            "set_server_count": ("setting_server_count", "🖥️ Send total server count (e.g. 2):"),
            "set_server_labels": ("setting_server_labels", "🏷️ Send Server labels, one per line:\n`Server | Tag | Bullet1; Bullet2; Bullet3`\nexample:\n`1 | Private Stock | Cheapest option; Directly managed`"),
            "set_toggle_server": ("setting_toggle_server", "🔌 Send: `Server | on` Or `Server | off`\nExample: `2 | on`"),
            "set_vnh_markup":   ("setting_vnh_markup", "📈 Send the VNH markup percent (e.g. `20` for 20%):"),
            "set_vip_discount": ("setting_vip_discount", "⭐ Send the VIP discount percent (e.g. `10` for 10% off):"),
            "set_year_cfg":     ("setting_year_cfg", "📅 Send: `Server | on/off | Year1,Year2,...`\nExample: `1 | on | 2021,2022,2023`\nExample: `2 | off`"),
            "set_per_row":      ("setting_per_row", "🔲 Send buttons per row (1 to 4):"),
            "set_logs_channel": ("setting_logs_channel", "📋 Forward a message from the logs channel, Or send its chat ID (e.g. -100123456789).\nMake sure the bot is added to that channel as admin first:"),
        }
        sk, prompt = _prompts[data]
        if data == "toggle_whatsapp":
            current = await get_setting("whatsapp_enabled", False)
            await set_setting("whatsapp_enabled", not current)
            await event.answer(f"✅ WhatsApp {'enabled' if not current else 'disabled'}")
            await event.edit(fancy("💬 **WhatsApp** Toggled."),
                             buttons=[[color_btn("◀️ Back", "asettings", "default")]])
            return
        elif data == "toggle_skip_server":
            cur = await get_setting("skip_server_step_if_one", False)
            await set_setting("skip_server_step_if_one", not cur)
            await event.answer(f"Skip-If-One-Server: {'ON' if not cur else 'OFF'}")
            await callback_router(event, "asettings")
            return
        elif data == "remove_upi":
            await set_setting("upi_id", "")
            await event.answer("✅ UPI ID removed.")
            await callback_router(event, "asettings")
            return
        elif data == "set_welcome_photo":
            user_states[user_id] = {"state": "welcome_photo_set"}
            await event.edit(prompt, buttons=[[color_btn("❌ Cancel", "asettings", "default")]])
            return
        user_states[user_id] = {"state": sk}
        await event.edit(fancy(prompt), buttons=[[color_btn("❌ Cancel", "asettings", "default")]])

    elif data == "acountries":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        c_list = await countries_col.find({}).to_list(50)
        rows   = []
        for c in c_list:
            em = "✅" if c.get("is_active") else "❌"
            rows.append([color_btn(f"{em} {c['flag']} {c['name']}", f"ctoggle:{c['code']}", "default")])
        rows.append([color_btn("💰 Change Price", "pr_cat", "success"),
                     color_btn("🏳️ Change Flag", "fl_pick", "success")])
        rows.append([color_btn(f"🏳️ Flags: {'ON' if _UI['flags'] else 'OFF'}", "flags_toggle", "success")])
        rows.append([color_btn("📞 Set Number Code", "dl_pick", "success"),
                     color_btn("📞 Auto-fill Codes", "dl_auto", "success")])
        rows.append([color_btn("➕ Add Country", "add_country", "default"),
                     color_btn("◀️ Back", "admin", "default")])
        await event.edit(fancy("🌍 **Countries** (tap to toggle):"), buttons=rows)

    elif data == "flags_toggle":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        _UI["flags"] = not _UI["flags"]
        await set_setting("show_flags", _UI["flags"])
        _ac_cache.clear()
        await event.answer(f"Flags {'ON' if _UI['flags'] else 'OFF'}")
        await callback_router(event, "acountries")

    elif data == "dl_pick":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        c_list = await countries_col.find({}).to_list(300)
        rows, row = [], []
        for c in c_list:
            d = str(c.get("dial") or "").strip()
            row.append(color_btn(f"{c['flag']} {c['name']}{' +' + d if d else ''}", f"dl_set:{c['code']}", "default"))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([color_btn("◀️ Back", "acountries", "default")])
        await event.edit(fancy("📞 **Number code**\n\nThe code (like +91) is shown on buttons only for countries where you set it."), buttons=rows)

    elif data == "dl_auto":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        n = 0
        async for c in countries_col.find({"$or": [{"dial": {"$exists": False}}, {"dial": ""}, {"dial": None}]}):
            if c["code"] in _DIAL:
                await countries_col.update_one({"code": c["code"]}, {"$set": {"dial": _DIAL[c["code"]]}})
                n += 1
        _ac_cache.clear()
        await event.answer(f"✅ Codes added for {n} countries", alert=True)

    elif data.startswith("dl_set:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        code = data.split(":", 1)[1]
        c = await countries_col.find_one({"code": code})
        if not c:
            await event.answer("❌ Not found.", alert=True)
            return
        user_states[user_id] = {"state": "edit_dial", "cc": code}
        await event.edit(fancy(f"📞 **{c['flag']} {c['name']}**\n\nSend the number code, e.g. `91` (send `-` to hide it):"),
                         buttons=[[color_btn("❌ Cancel", "dl_pick", "default")]])

    elif data == "fl_pick":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        c_list = await countries_col.find({}).to_list(300)
        rows, row = [], []
        for c in c_list:
            row.append(color_btn(f"{c['flag']} {c['name']}", f"fl_set:{c['code']}", "default"))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([color_btn("◀️ Back", "acountries", "default")])
        await event.edit(fancy("🏳️ **Change flag**\n\nSelect a country:"), buttons=rows)

    elif data.startswith("fl_set:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        code = data.split(":", 1)[1]
        c = await countries_col.find_one({"code": code})
        if not c:
            await event.answer("❌ Not found.", alert=True)
            return
        user_states[user_id] = {"state": "edit_flag", "cc": code}
        await event.edit(fancy(f"🏳️ **{c['flag']} {c['name']}**\n\nSend the new flag emoji (example: 🇮🇳):"),
                         buttons=[[color_btn("❌ Cancel", "fl_pick", "default")]])

    elif data == "pr_cat":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        cats = await categories_col.find({}).sort("order", 1).to_list(50)
        rows = [[color_btn(f"{c['icon']} {c['name']}", f"pr_c:{c['name']}", "default")] for c in cats]
        rows.append([color_btn("◀️ Back", "acountries", "default")])
        await event.edit(fancy("💰 **Change price**\n\nSelect category:"), buttons=rows)

    elif data.startswith("pr_c:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        cat_name = data.split(":", 1)[1]
        c_list = await countries_col.find({}).to_list(300)
        prices = {d["code"]: d["price"] async for d in cat_prices_col.find({"category": cat_name})}
        rows, row = [], []
        for c in c_list:
            pr = prices.get(c["code"], c.get("price", 0))
            row.append(color_btn(f"{c['flag']} {c['name']} • {float(pr or 0):g}", f"pr_set:{c['code']}:{cat_name}", "default"))
            if len(row) == 2:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([color_btn("◀️ Back", "pr_cat", "default")])
        await event.edit(fancy(f"💰 **{cat_name}** — select country:"), buttons=rows)

    elif data.startswith("pr_set:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        _, code, cat_name = data.split(":", 2)
        c = await countries_col.find_one({"code": code})
        if not c:
            await event.answer("❌ Not found.", alert=True)
            return
        cur = await get_cat_price(code, cat_name, c.get("price", 0))
        user_states[user_id] = {"state": "edit_cat_price", "cc": code, "cat": cat_name}
        await event.edit(
            fancy(f"💰 **{c['flag']} {c['name']} • {cat_name}**\n\nCurrent: `₹{float(cur or 0):g}`\n\nSend the new price in ₹:"),
            buttons=[[color_btn("❌ Cancel", f"pr_c:{cat_name}", "default")]])

    elif data.startswith("ctoggle:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        code = data.split(":")[1]
        c    = await countries_col.find_one({"code": code})
        if not c:
            await event.answer("❌ Not found.", alert=True)
            return
        new  = not c.get("is_active", True)
        await countries_col.update_one({"code": code}, {"$set": {"is_active": new}})
        await event.answer(f"{'Enabled' if new else 'Disabled'} {code}")
        await callback_router(event, "acountries")

    elif data == "acategories":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        cat_list = await categories_col.find({}).sort("order", 1).to_list(50)
        rows = []
        for cat in cat_list:
            em = "✅" if cat.get("is_active") else "❌"
            yr_on = await _cat_has_year(cat['name'])
            rows.append([color_btn(f"{em} #{cat.get('order', 0)} {cat['icon']} {cat['name']}", f"cattoggle:{cat['name']}", "default"),
                         color_btn(f"📅 Year {'ON' if yr_on else 'OFF'}", f"catyear:{cat['name']}", "success" if yr_on else "default"),
                         color_btn("🗑️", f"catdel:{cat['name']}", "default")])
        rows.append([color_btn("➕ Add Category", "add_category", "default"),
                     color_btn("◀️ Back", "admin", "default")])
        await event.edit(fancy("🗂️ **Categories** (tap to toggle):"), buttons=rows)

    elif data.startswith("cattoggle:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        name = data.split(":", 1)[1]
        cat  = await categories_col.find_one({"name": name})
        if not cat:
            await event.answer("❌ Not found.", alert=True)
            return
        new = not cat.get("is_active", True)
        await categories_col.update_one({"name": name}, {"$set": {"is_active": new}})
        await event.answer(f"{'Enabled' if new else 'Disabled'} {name}")
        await callback_router(event, "acategories")

    elif data.startswith("catyear:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        name = data.split(":", 1)[1]
        new = not await _cat_has_year(name)
        await categories_col.update_one({"name": name}, {"$set": {"has_year": new}})
        _cat_year_cache[name] = new
        await event.answer(f"Year step {'ON' if new else 'OFF'} for {name}")
        await callback_router(event, "acategories")

    elif data.startswith("catdel:"):
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        name = data.split(":", 1)[1]
        stock_left = await accounts_col.count_documents({"category": name, "status": "available"})
        if stock_left > 0:
            await event.answer(f"❌ {stock_left} account(s) still use this category — disable it instead of deleting.", alert=True)
            return
        await categories_col.delete_one({"name": name})
        await event.answer(f"Deleted {name}")
        await callback_router(event, "acategories")

    elif data == "add_category":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        user_states[user_id] = {"state": "add_category"}
        await event.edit(
            fancy("🗂️ **Add / Edit Category**\n\nSend:\n`Name | Icon | Order (optional)`\nExample: `Premium | 💎 | 1`\n\nUsing an existing name updates it (And Re-Enables it if off)."),
            buttons=[[color_btn("❌ Cancel", "acategories", "default")]],
        )

    elif data == "add_country":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        user_states[user_id] = {"state": "add_country"}
        await event.edit(
            fancy("🌍 **Add country**\n\nsend:\nSend just the country **name** or **code**.\nExample: `Turkey` or `TR`\n\n(Flag is automatic. Price is set per category when you upload stock.)"),
            buttons=[[color_btn("❌ Cancel", "acountries", "default")]],
        )

    elif data == "ausers":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        user_states[user_id] = {"state": "search_user"}
        await event.edit(
            fancy("👤 **User Lookup**\n\nSend the telegram user ID:"),
            buttons=[
                [color_btn("💰 Add Balance", "admin_add_bal", "default"),
                 color_btn("🚫 Ban/Unban", "admin_ban", "default")],
                [color_btn("◀️ Back", "admin", "default")],
            ],
        )

    elif data == "admin_add_bal":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        user_states[user_id] = {"state": "add_bal_uid"}
        await event.edit(fancy("💰 **Add Balance**\n\nSend the member's Telegram user ID:"),
            buttons=[[color_btn("❌ Cancel", "admin", "default")]])

    elif data == "admin_ban":
        if not await is_admin(user_id):
            await event.answer("❌ Access denied.", alert=True)
            return
        user_states[user_id] = {"state": "ban_uid"}
        await event.edit(fancy("🚫 **Ban/unban**\n\nsend user ID:"),
            buttons=[[color_btn("❌ Cancel", "admin", "default")]])

    elif data == "manage_admins":
        if user_id != OWNER_ID:
            await event.answer("❌ Owner only!", alert=True)
            return
        admins = await bot_admins_col.find({"is_active": True}).to_list(50)
        rows   = []
        for a in admins:
            rows.append([color_btn(f"🔴 Remove {a.get('name', a['telegram_id'])}", f"rm_admin:{a['telegram_id']}", "default")])
        rows.append([color_btn("➕ Add Admin", "add_admin", "default"),
                     color_btn("◀️ Back", "admin", "default")])
        await event.edit(fancy(f"🔑 **Manage admins**\n\nowner: `{OWNER_ID}`\nextra admins: {len(admins)}"), buttons=rows)

    elif data == "add_admin":
        if user_id != OWNER_ID:
            await event.answer("❌ Owner only!", alert=True)
            return
        user_states[user_id] = {"state": "add_admin"}
        await event.edit(fancy("🔑 **Add Admin**\n\nsend telegram user ID:"),
            buttons=[[color_btn("❌ Cancel", "manage_admins", "default")]])

    elif data.startswith("rm_admin:"):
        if user_id != OWNER_ID:
            await event.answer("❌ Owner only!", alert=True)
            return
        rm_id = int(data.split(":")[1])
        await bot_admins_col.update_one({"telegram_id": rm_id}, {"$set": {"is_active": False}})
        await event.answer(f"Removed admin {rm_id}")
        try:
            await bot.send_message(rm_id, "🔑 Your admin access has been removed.")
        except Exception:
            pass
        admins = await bot_admins_col.find({"is_active": True}).to_list(50)
        rows   = [[color_btn(f"🔴 Remove {a.get('name', a['telegram_id'])}", f"rm_admin:{a['telegram_id']}", "default")] for a in admins]
        rows.append([color_btn("➕ Add Admin", "add_admin", "default"),
                     color_btn("◀️ Back", "admin", "default")])
        await event.edit(fancy("🔑 **Manage Admins**:"), buttons=rows)

    elif data == "balance":
        if not user:
            user = await get_or_create_user(user_id)
        bal   = float(user.get("balance", 0))
        spent = 0.0
        async for o in orders_col.find({"user_id": user_id, "status": {"$nin": ["cancelled"]}}):
            spent += float(o.get("amount", 0))
        deposited = 0.0
        async for d in deposits_col.find({"user_id": user_id, "status": "approved"}):
            deposited += float(d.get("credits") or d.get("amount") or 0)
        await event.edit(
            RAW + "**WALLET**\n\n"
            f"{LINE}\n"
            f"Balance   : **₹{bal:.2f}**\n"
            f"Deposited : ₹{deposited:.2f}\n"
            f"Spent     : ₹{spent:.2f}\n"
            f"{LINE}",
            buttons=[
                [color_btn("Add Funds", "deposit", "success"),
                 color_btn("Transactions", "history", "primary")],
                [color_btn("Back", "main_menu", "success")],
            ],
        )

    else:
        await event.answer()

# ─── 19. DEPOSIT CREDITING (webhook-driven, real payment only) ──
async def _credit_deposit_by_id(dep_object_id, notify: bool = True, delete_ui: bool = True,
                                payment_id: Optional[str] = None) -> bool:
    """Atomically flips a pending deposit (by Mongo _id) to approved and credits the
    user. Returns False if it was already processed (prevents double-credit).
    A verified Razorpay payment id can only ever be attached to ONE deposit."""
    set_ = {"status": "approved", "approved_at": datetime.utcnow(), "approved_via": "razorpay"}
    if payment_id:
        set_["payment_id"] = payment_id
    try:
        result = await deposits_col.update_one({"_id": dep_object_id, "status": "pending"}, {"$set": set_})
    except DuplicateKeyError:
        log.critical(f"Razorpay payment reused across deposits: {payment_id} / {dep_object_id}")
        await log_event(f"🚨 **Razorpay payment `{payment_id}` already used** — deposit `{dep_object_id}` NOT credited. Review manually.")
        return False
    if result.modified_count == 0:
        return False
    dep = await deposits_col.find_one({"_id": dep_object_id})
    uid = dep["user_id"]
    amount = dep["amount"]
    credits = dep.get("credits", 0)
    await users_col.update_one({"user_id": uid}, {"$inc": {"balance": amount}})
    await referral_first_deposit_bonus(uid, amount)
    await sync_payment_group_message(dep, "✅ **AUTO-APPROVED** (Razorpay API verified)")
    if delete_ui:
        await _cleanup_temp(uid)
        await _delete_msg(uid, dep.get("ui_msg_id"))
        user_states.pop(uid, None)
    if notify:
        try:
            await bot.send_message(
                uid, fancy(f"✅ **Payment confirmed!**\n`₹{credits}` added to your wallet."),
                buttons=[[color_btn("🏠 Home", "main_menu", "default")]])
        except Exception:
            pass
    await log_event(f"💰 **Deposit Added**\n• User: `{uid}`\n• ₹{amount:.2f} → +₹{credits}\n• Via: Razorpay (verified)")
    await ext_close_deposit_source(dep)
    return True

# ─── 20. TEXT / FILE MESSAGE HANDLER ─────────────────────────────
@bot.on(events.NewMessage())
async def message_handler(event):
    text = event.message.text or ""
    if text.startswith("/"):
        return

    user_id    = event.sender_id
    state_data = user_states.get(user_id)
    if not state_data:
        return

    state = state_data.get("state") if isinstance(state_data, dict) else state_data

    if isinstance(state_data, dict) and await ext_message(event, user_id, state_data):
        return

    if state == "vnh_search":
        _consume_prompt(event, user_id)
        user_states[user_id] = {"server": state_data.get("server", 2)}
        await event.respond(fancy(f"🔍 Results For `{text.strip()}`:"))
        class _FakeEvent:
            async def edit(self2, *a, **kw):
                return await event.respond(*a, **kw)
        await _send_vnh_country_list(_FakeEvent(), user_id, 0, text.strip())
        return

    if state == "edit_dial":
        val = text.strip().lstrip("+")
        if val == "-":
            val = ""
        elif not (val.isdigit() and len(val) <= 5):
            await event.respond(fancy("❌ Send digits only, e.g. `91` (or `-` to hide)"))
            return
        await countries_col.update_one({"code": state_data["cc"]}, {"$set": {"dial": val}})
        _ac_cache.clear()
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ Number code " + (f"set to +{val}" if val else "hidden")),
                            buttons=[[color_btn("◀️ Codes", "dl_pick", "default")]])
        return

    if state == "edit_flag":
        val = text.strip()
        if not val or len(val) > 16 or val.isascii():
            await event.respond(fancy("❌ Send a flag emoji, e.g. 🇮🇳"))
            return
        await countries_col.update_one({"code": state_data["cc"]}, {"$set": {"flag": val}})
        _ac_cache.clear()
        user_states.pop(user_id, None)
        await event.respond(fancy(f"✅ Flag updated: {val}"), buttons=[[color_btn("◀️ Flags", "fl_pick", "default")]])
        return

    if state == "edit_cat_price":
        try:
            val = float(text.strip().replace(",", "."))
            if val <= 0 or val > 100000:
                raise ValueError
        except Exception:
            await event.respond(fancy("❌ Send a valid price, e.g. `30`"))
            return
        await set_cat_price(state_data["cc"], state_data["cat"], val)
        user_states.pop(user_id, None)
        await event.respond(fancy(f"✅ Price updated: **{state_data['cat']}** • `{state_data['cc']}` → `₹{val:g}`"),
                            buttons=[[color_btn("◀️ Prices", f"pr_c:{state_data['cat']}", "default")]])
        return

    if state == "add_country_cat":
        srv_n, cat_name = state_data["srv"], state_data["cat"]
        raw_txt = text.strip()
        if "|" in raw_txt:                          # old style `CODE | Name` still works
            pp = [x.strip() for x in raw_txt.split("|")]
            r = {"code": pp[0].upper(), "name": pp[1] if len(pp) > 1 and pp[1] else pp[0].upper(),
                 "flag": COUNTRY_FLAGS.get(pp[0].upper()) or _flag_for(pp[0])}
        else:
            r = resolve_country(raw_txt)
        if not r.get("code"):
            hint = ("\n\nDid you mean: " + ", ".join(f"`{x}`" for x in r["suggest"])) if r.get("suggest") else ""
            await event.respond(fancy("❌ Country not recognised." + hint + "\n\nSend the full name or the 2-letter code."))
            return
        doc = await _ensure_country(r)
        user_states.pop(user_id, None)
        class _MsgCb(_EditAsNew):
            async def answer(self2, *a, **kw):
                return None
        await callback_router(_MsgCb(event), f"upload_country:{srv_n}:{doc['code']}:{cat_name}")
        return

    if state == "set_cat_price":
        try:
            val = float(text.strip().replace(",", "."))
            if val <= 0 or val > 100000:
                raise ValueError
        except Exception:
            await event.respond(fancy("❌ Send a valid price, e.g. `30`"))
            return
        await set_cat_price(state_data["cc"], state_data["cat"], val)
        user_states.pop(user_id, None)
        class _FE:
            async def edit(self2, *a, **kw):
                return await event.respond(*a, **kw)
            async def answer(self2, *a, **kw):
                return None
        await _begin_upload(_FE(), user_id, state_data["srv"], state_data["cc"], state_data["cat"], state_data.get("year"))
        return

    if state == "store_search":
        _consume_prompt(event, user_id)
        state_data.pop("state", None)
        state_data["search"] = text.strip()
        class _FakeEv:
            async def edit(self2, *a, **kw):
                return await event.respond(*a, **kw)
        await _send_country_list(_FakeEv(), user_id, 0)
        return

    if state == "await_deposit_screenshot":
        if not (event.message.photo or event.message.document):
            await event.respond(fancy("❌ Please send a photo screenshot."),
                                 buttons=[[color_btn("❌ Cancel", "cancel_payment", "default")]])
            return
        amount  = state_data.get("amount", 0)
        credits = state_data.get("credits", 0)
        txn_id  = state_data.get("txn_id", "N/A")
        dep_id  = state_data.get("deposit_id_obj")
        if dep_id:
            await deposits_col.update_one({"_id": ObjectId(dep_id)}, {"$set": {"screenshot_sent_at": datetime.utcnow()}})
        else:
            dep = await deposits_col.insert_one({
                "user_id": user_id, "amount": amount, "credits": credits,
                "method": "manual", "txn_id": txn_id, "status": "pending",
                "created_at": datetime.utcnow(),
            })
            dep_id = str(dep.inserted_id)
        try:
            photo_bytes = await event.message.download_media(bytes)
        except Exception as e:
            log.error(f"[manual deposit] download failed: {e}")
            photo_bytes = None
        delivered = await send_deposit_proof(photo_bytes, user_id, amount, credits, txn_id, dep_id,
                                             kind=state_data.get("kind", "UPI QR"))
        if not delivered:
            await event.respond(fancy("⚠️ Could not reach the admins right now. Please send the screenshot again in a minute."))
            return
        user_states.pop(user_id, None)
        await _cleanup_temp(user_id)
        await _delete_msg(user_id, state_data.get("ui_msg_id"))
        await event.respond(
            fancy(f"✅ **Screenshot received!**\n\nAdmin will verify your ₹{amount:.2f} deposit shortly."),
            buttons=[[color_btn("🏠 Home", "main_menu", "default")]]
        )
        return

    if state == "custom_deposit":
        try:
            amount = float(text.strip().replace(",", ""))
        except ValueError:
            await event.respond("Please send a valid number.")
            return
        min_d, max_d = await _deposit_limits()
        if amount < min_d:
            await event.respond(f"Minimum deposit is ₹{min_d:g}.")
            return
        if amount > max_d:
            await event.respond(f"Maximum deposit is ₹{max_d:g}.")
            return
        credits = int(amount // 1)
        method = state_data.get("method") or ("auto" if (RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET) else None)
        await _delete_msg(user_id, state_data.get("prompt_id"))
        try:
            await event.delete()
        except Exception:
            pass
        if method in ("auto", "manual"):
            user_states.pop(user_id, None)
            msg = await event.respond("Creating your payment link…")
            ui = _MsgUI(msg, user_id)
            if method == "auto":
                await _start_razorpay_auto_deposit(ui, user_id, amount, credits)
            else:
                await _start_manual_deposit(ui, user_id, amount, credits)
            return
        user_states[user_id] = {"custom_amount": amount, "custom_credits": credits}
        await event.respond(
            fancy(
                "💳 **Select Payment Method**\n\n"
                f"Amount: `₹{amount:.2f}`\n\n"
                "UPI · Manual — pay, send screenshot, Admin approves."
            ),
            buttons=[
                [color_btn("UPI · Manual", "pay_method_custom:manual", "primary")],
                [color_btn("Back", "deposit_pkgs", "success")]
            ]
        )

    elif state == "waiting_zip" and not event.message.file:
        if not await is_admin(user_id):
            user_states.pop(user_id, None)
            return
        twofa = text.strip()
        user_states[user_id] = {**state_data, "twofa_password": twofa}
        await event.respond(
            fancy(f"🔐 2FA password saved: `{twofa}`\n\nnow send the **.zip** or **.session** file."),
            buttons=[[color_btn("❌ Cancel", "admin", "default")]],
        )

    elif state == "waiting_zip" and (event.message.file or event.message.media):
        if not await is_admin(user_id):
            user_states.pop(user_id, None)
            return
        prog = await event.respond(fancy("⏳ Downloading File…"))
        try:
            file_bytes = await event.message.download_media(bytes)
        except Exception as e:
            await prog.edit(f"❌ Download Failed: {e}")
            return

        if event.message.file and event.message.file.name and event.message.file.name.lower().endswith('.session'):
            ss = await _session_file_to_string(file_bytes)
            if not ss:
                await prog.edit("❌ Invalid session file.")
                user_states.pop(user_id, None)
                return
            phone = _phone_from_filename(event.message.file.name)
            res = await _register_uploaded_account(user_id, _upload_ctx(state_data), phone, ss,
                                                   state_data.get("twofa_password", ""))
            if res == "added":
                await prog.edit(fancy(f"✅ **File uploaded**\n`{phone}` added to {state_data['country_name']}."))
                await log_event(f"📦 **Stock Added**\n• Admin: `{user_id}`\n• Phone: `{phone}`\n• {state_data['country_name']} • {state_data['category']}\n• Added: 1")
                await announce_stock_update(_upload_ctx(state_data), 1)
            else:
                await prog.edit(fancy(f"⚠️ `{phone}` skipped — {'already in stock' if res == 'duplicate' else 'session is invalid'}."))
            user_states.pop(user_id, None)
            return

        try:
            zf = zipfile.ZipFile(io.BytesIO(file_bytes))
        except Exception as e:
            await prog.edit(f"❌ Invalid ZIP: {e}")
            user_states.pop(user_id, None)
            return

        twofa = state_data.get("twofa_password", "")
        try:
            info = zf.getinfo("2fa.txt")
            twofa = zf.read(info).decode().strip()
        except KeyError:
            pass
        if not twofa:
            twofa = await get_setting("default_2fa", "")

        all_names = [n for n in zf.namelist() if n.lower().endswith(".session")]
        if not all_names:
            await prog.edit("❌ No .session files found in ZIP.")
            user_states.pop(user_id, None)
            return

        total = len(all_names)
        sem = asyncio.Semaphore(5)
        added = 0
        skipped = 0
        errors = []

        async def process_one(name):
            nonlocal added, skipped
            async with sem:   # cap concurrent session logins/DB writes at 5 — a large
                              # ZIP shouldn't try to open hundreds of Telegram clients at once
                phone = _phone_from_filename(name)
                try:
                    raw_bytes = zf.read(name)
                except Exception:
                    errors.append(phone)
                    skipped += 1
                    return
                ss = await _session_file_to_string(raw_bytes)
                if not ss:
                    errors.append(phone)
                    skipped += 1
                    return
                res = await _register_uploaded_account(user_id, _upload_ctx(state_data), phone, ss, twofa)
                if res != "added":
                    skipped += 1
                    if res == "invalid":
                        errors.append(phone)
                    return
                added += 1

        tasks = [process_one(n) for n in all_names]
        await asyncio.gather(*tasks)

        result = fancy(f"📦 **Upload complete**\n\n✅ added: `{added}`\n⏭️ skipped: `{skipped}`\n")
        if errors:
            shown = errors[:5]
            result += f"❌ Failed ({len(errors)}): `{', '.join(shown)}`"
        await prog.edit(result, buttons=[[color_btn("◀️ Admin", "admin", "default")]])
        user_states.pop(user_id, None)
        zf.close()
        if added:
            await log_event(f"📦 **Stock Added**\n• Admin: `{user_id}`\n• {state_data['country_name']} • {state_data['category']}\n• Added: {added} • Skipped: {skipped}")
            await announce_stock_update(_upload_ctx(state_data), added)

    elif state == "broadcast":
        user_states.pop(user_id, None)
        prog  = await event.respond(fancy("📢 Broadcasting…"))
        count = 0
        fail  = 0
        async for u in users_col.find({}, {"user_id": 1}):
            try:
                await bot.send_message(u["user_id"], text)
                count += 1
            except Exception:
                fail += 1
            if (count + fail) % 50 == 0:
                try:
                    await prog.edit(f"📢 Broadcasting… {count} Sent, {fail} Failed")
                except Exception:
                    pass
            await asyncio.sleep(0.05)
        await prog.edit(fancy(f"✅ Broadcast complete — {count} sent, {fail} failed."))

    elif state == "setting_botname":
        await set_setting("bot_name", text.strip())
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ Bot Name Updated."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_upi":
        val = text.strip()
        if val.lower() in ("remove", "clear", "none", "-", "delete"):
            await set_setting("upi_id", "")
            user_states.pop(user_id, None)
            await event.respond(fancy("✅ UPI ID cleared. manual deposits are disabled until you set a new one."),
                                buttons=[[color_btn("◀️ Settings", "asettings", "default")]])
            return
        if "@" not in val or " " in val or len(val) < 5:
            await event.respond(fancy(
                "❌ That doesn't look like a valid UPI ID (should look like `name@bank`).\n"
                "Send a valid UPI ID, or send `remove` to clear it."
            ))
            return
        await set_setting("upi_id", val)
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ UPI ID Updated."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_upiname":
        await set_setting("upi_name", text.strip())
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ UPI Name Updated."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_support":
        await set_setting("support_link", text.strip())
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ Support Link Updated."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_ref_bonus":
        try:
            val = float(text.strip())
            await set_setting("referral_bonus", val)
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ Referral bonus set to ₹{val:.0f}."),
                                buttons=[[color_btn("◀️ Settings", "asettings", "default")]])
        except ValueError:
            await event.respond(fancy("❌ Send a valid number."))

    elif state == "setting_ref_pct":
        try:
            val = float(text.strip())
            await set_setting("referral_percent", val)
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ Referral % Set to {val:.1f}%."),
                                buttons=[[color_btn("◀️ Settings", "asettings", "default")]])
        except ValueError:
            await event.respond(fancy("❌ Send a valid number."))

    elif state == "setting_min_dep":
        try:
            val = float(text.strip())
            await set_setting("min_deposit", val)
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ Minimum deposit set to ₹{val:.0f}."),
                                buttons=[[color_btn("◀️ Settings", "asettings", "default")]])
        except ValueError:
            await event.respond(fancy("❌ Send a valid number."))

    elif state == "setting_max_dep":
        try:
            val = float(text.strip())
            await set_setting("max_deposit", val)
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ Maximum deposit set to ₹{val:.0f}."),
                                buttons=[[color_btn("◀️ Settings", "asettings", "default")]])
        except ValueError:
            await event.respond(fancy("❌ Send a valid number."))

    elif state == "setting_sales":
        link = text.strip()
        await set_setting("sales_link", "" if link == "-" else link)
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ Sales Link Updated."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_server_count":
        try:
            val = int(text.strip())
            if val < 1:
                raise ValueError
            await set_setting("server_count", val)
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ Server count set to {val}."),
                                buttons=[[color_btn("◀️ Settings", "asettings", "default")]])
        except ValueError:
            await event.respond(fancy("❌ Send a valid number (1 Or More)."))

    elif state == "setting_vip_discount":
        try:
            val = float(text.strip())
            if not 0 <= val <= 100:
                raise ValueError
        except ValueError:
            await event.respond(fancy("❌ Send a number between 0 and 100."))
            return
        await set_setting("vip_discount_percent", val)
        user_states.pop(user_id, None)
        await event.respond(fancy(f"✅ VIP discount set to {val}%."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_vnh_markup":
        try:
            val = float(text.strip())
            if val < 0:
                raise ValueError
        except ValueError:
            await event.respond(fancy("❌ Send a valid non-negative number, e.g. `20`."))
            return
        await vnh_server.set_markup_percent(val)
        user_states.pop(user_id, None)
        await event.respond(fancy(f"✅ VNH markup set to {val}%."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_toggle_server":
        try:
            srv, onoff = [p.strip() for p in text.split("|", 1)]
            srv_n = int(srv)
            on = onoff.lower() in ("on", "yes", "true", "1", "enable", "enabled", "active")
        except Exception:
            await event.respond(fancy("❌ Wrong format. use:\n`Server | on` or `Server | off`"))
            return
        cur = await get_setting("server_active", None)
        cur = cur if isinstance(cur, dict) else {}
        cur[str(srv_n)] = on
        await set_setting("server_active", cur)
        user_states.pop(user_id, None)
        await event.respond(fancy(f"✅ Server {srv_n} Is Now {'Active ✅' if on else 'Inactive ❌'}."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_server_labels":
        labels = {}
        for line in text.splitlines():
            parts = [p.strip() for p in line.split("|")]
            if len(parts) >= 3 and parts[0].isdigit() and parts[1] and parts[2]:
                bullets = [b.strip() for b in parts[2].split(";") if b.strip()]
                if bullets:
                    labels[parts[0]] = {"tag": parts[1], "bullets": bullets}
        if not labels:
            await event.respond(fancy(
                "❌ Wrong Format. Use:\n"
                "`1 | Private Stock | Cheapest option; Directly managed`\n"
                "`2 | External Server | Third-party stock; Live rates`"
            ))
            return
        cur = await get_setting("server_labels", None)
        cur = cur if isinstance(cur, dict) else {}
        cur.update(labels)
        await set_setting("server_labels", cur)
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ Server Labels Saved."), buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_year_cfg":
        try:
            parts = [p.strip() for p in text.split("|")]
            srv = int(parts[0])
            enabled = parts[1].lower() in ("on", "yes", "true", "1", "enable", "enabled")
            years = None
            if len(parts) > 2 and parts[2]:
                years = [y.strip() for y in parts[2].split(",") if y.strip()]
            kwargs = {"enabled": enabled}
            if years:
                kwargs["years"] = years
            await _set_server_year_cfg(srv, **kwargs)
            user_states.pop(user_id, None)
            await event.respond(
                fancy(f"✅ Server {srv} Year Step: {'ON' if enabled else 'OFF'}" + (f" (`{', '.join(years)}`)" if years else "")),
                buttons=[[color_btn("◀️ Settings", "asettings", "default")]]
            )
        except Exception:
            await event.respond(fancy("❌ Wrong Format. Use:\n`Server | on/off | Year1,Year2,...`"))

    elif state == "setting_per_row":
        try:
            val = int(text.strip())
            if not 1 <= val <= 4:
                raise ValueError
        except ValueError:
            await event.respond(fancy("❌ Send a number from 1 to 4."))
            return
        await set_setting("buttons_per_row", val)
        user_states.pop(user_id, None)
        await event.respond(fancy(f"✅ Buttons per row set to {val}."), buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_logs_channel":
        chat_id = None
        if event.message.forward and event.message.forward.chat_id:
            chat_id = event.message.forward.chat_id
        else:
            try:
                chat_id = int(text.strip())
            except ValueError:
                pass
        if not chat_id:
            await event.respond(fancy("❌ Could not detect a channel ID. Forward a message from the channel, Or send the ID directly."))
            return
        try:
            await bot.send_message(chat_id, fancy("✅ This channel is now connected as the logs channel."))
        except Exception as e:
            await event.respond(fancy(f"❌ Could not send to that chat — Is the bot added as admin there? ({e})"))
            return
        await set_setting("logs_channel_id", chat_id)
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ Logs Channel Saved."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "setting_default_2fa":
        await set_setting("default_2fa", text.strip())
        user_states.pop(user_id, None)
        await event.respond(fancy("✅ Default 2FA password set."),
                            buttons=[[color_btn("◀️ Settings", "asettings", "default")]])

    elif state == "welcome_photo_set":
        if event.message.photo:
            if hasattr(event.message.media, 'photo') and hasattr(event.message.media.photo, 'id'):
                file_id = str(event.message.media.photo.id)
                await set_setting("welcome_photo", file_id)
                user_states.pop(user_id, None)
                await event.respond(fancy("🖼️ Welcome Photo Set!"),
                                    buttons=[[color_btn("◀️ Settings", "asettings", "default")]])
            else:
                await event.respond(fancy("❌ Unable to get photo ID."))
        else:
            await event.respond(fancy("❌ Please send a photo."))

    elif state == "add_country":
        try:
            parts = [p.strip() for p in text.strip().split("|")]
            if len(parts) == 1:                      # just a name or a code
                r = resolve_country(parts[0])
                if not r.get("code"):
                    hint = ("\n\nDid you mean: " + ", ".join(f"`{x}`" for x in r["suggest"])) if r.get("suggest") else ""
                    await event.respond(fancy("❌ Country not recognised." + hint + "\n\nSend the full name or the 2-letter code."))
                    return
                parts = [r["code"], r["name"]]
            code, name = parts[0].upper(), parts[1]
            existing  = await countries_col.find_one({"code": code})
            if existing and len(parts) == 2:
                name = existing["name"]
            flag_     = parts[2] if len(parts) > 2 and parts[2] else (existing or {}).get("flag") or COUNTRY_FLAGS.get(code, "🌍")
            price_val = float((existing or {}).get("price", 0) or 0)      # price is per category now — never edited here
            if existing:
                await countries_col.update_one({"code": code}, {"$set": {"name": name, "flag": flag_, "price": price_val, "is_active": True}})
                msg = f"♻️ **{name}** Updated."
            else:
                await countries_col.insert_one({"code": code, "name": name, "flag": flag_, "price": price_val, "is_active": True})
                msg = f"✅ **{name}** Added. Set its price per category from 💰 Change Price or while uploading."
            user_states.pop(user_id, None)
            await event.respond(fancy(msg), buttons=[[color_btn("◀️ Countries", "acountries", "default")]])
        except Exception:
            await event.respond(fancy("❌ Wrong Format. Use:\n`CODE | Name`"))

    elif state == "add_category":
        try:
            parts = [p.strip() for p in text.strip().split("|")]
            name, icon = parts[0], parts[1]
            order_val = int(parts[2]) if len(parts) > 2 and parts[2].strip().lstrip("-").isdigit() else None
            existing = await categories_col.find_one({"name": name})
            if existing:
                upd = {"icon": icon, "is_active": True}
                if order_val is not None:
                    upd["order"] = order_val
                await categories_col.update_one({"name": name}, {"$set": upd})
                msg = f"♻️ **{name}** Updated."
            else:
                if order_val is None:
                    order_val = await categories_col.count_documents({}) + 1
                await categories_col.insert_one({"name": name, "icon": icon, "is_active": True, "order": order_val})
                msg = f"✅ **{name}** Added (Order {order_val})."
            user_states.pop(user_id, None)
            await event.respond(fancy(msg), buttons=[[color_btn("◀️ Categories", "acategories", "default")]])
        except Exception:
            await event.respond(fancy("❌ Wrong Format. Use:\n`Name | Icon | Order(optional)`"))

    elif state == "search_user":
        try:
            tid    = int(text.strip())
            target = await users_col.find_one({"user_id": tid})
            if not target:
                await event.respond(fancy("❌ User Not Found."))
                return
            o_count = await orders_col.count_documents({"user_id": tid})
            d_count = await deposits_col.count_documents({"user_id": tid})
            banned_ = "🚫 Yes" if target.get("is_banned") else "✅ No"
            vip_ = "⭐ Yes" if target.get("is_vip") else "No"
            await event.respond(
                fancy(f"👤 **User Info**\n\n• ID: `{tid}`\n• Balance: `₹{target.get('balance', 0):.2f}`\n• Orders: `{o_count}`\n• Deposits: `{d_count}`\n• Banned: {banned_}\n• Vip: {vip_}\n• Joined: {target.get('joined_at','?')}"),
                buttons=[[color_btn(
                    "⭐ Revoke Vip" if target.get("is_vip") else "⭐ Make Vip",
                    f"vip_toggle:{tid}", "default")]]
            )
            user_states.pop(user_id, None)
        except ValueError:
            await event.respond(fancy("❌ Send a valid telegram ID."))

    elif state == "add_bal_uid":
        try:
            tid = int(text.strip())
            if not await users_col.find_one({"user_id": tid}, {"_id": 1}):
                await event.respond(fancy("❌ User not found. They must start the bot first."))
                return
            user_states[user_id] = {"state": "add_bal_amount", "target_id": tid}
            await event.respond(fancy(f"💰 How much ₹ to add for user `{tid}`?"))
        except ValueError:
            await event.respond(fancy("❌ Invalid Telegram ID."))

    elif state == "add_bal_amount":
        try:
            amount  = float(text.strip())
            tid     = state_data["target_id"]
            if amount <= 0 or amount > 1_000_000:
                await event.respond(fancy("❌ Enter a positive amount."))
                return
            await users_col.update_one({"user_id": tid}, {"$inc": {"balance": amount}})
            with contextlib.suppress(Exception):
                await log_event(f"💰 **Balance Added**\n• Admin: `{user_id}`\n• User: `{tid}`\n• Amount: `₹{amount:g}`")
            try:
                await bot.send_message(tid, fancy(f"💰 **₹{amount:.0f} Added** To your wallet by admin!"))
            except Exception:
                pass
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ ₹{amount:.0f} Added to User `{tid}`."),
                                buttons=[[color_btn("◀️ Admin", "admin", "default")]])
        except ValueError:
            await event.respond(fancy("❌ Invalid Amount."))

    elif state == "ban_uid":
        try:
            tid    = int(text.strip())
            target = await users_col.find_one({"user_id": tid})
            if not target:
                await event.respond(fancy("❌ User Not Found."))
                user_states.pop(user_id, None)
                return
            new_ban = not target.get("is_banned", False)
            await users_col.update_one({"user_id": tid}, {"$set": {"is_banned": new_ban}})
            action = "Banned" if new_ban else "Unbanned"
            try:
                await bot.send_message(tid, fancy("🚫 You have been **banned** from this bot." if new_ban else "✅ You have been **unbanned**. welcome back!"))
            except Exception:
                pass
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ User `{tid}` Has Been **{action}**."),
                                buttons=[[color_btn("◀️ Admin", "admin", "default")]])
        except ValueError:
            await event.respond(fancy("❌ Invalid Telegram ID."))

    elif state == "add_admin":
        try:
            new_id = int(text.strip())
            try:
                entity = await bot.get_entity(new_id)
                name_  = getattr(entity, "first_name", str(new_id))
                uname_ = getattr(entity, "username", None)
            except Exception:
                name_  = str(new_id)
                uname_ = None
            existing = await bot_admins_col.find_one({"telegram_id": new_id})
            if existing:
                await bot_admins_col.update_one({"telegram_id": new_id}, {"$set": {"is_active": True}})
            else:
                await bot_admins_col.insert_one({"telegram_id": new_id, "name": name_, "username": uname_, "is_active": True, "added_by": user_id, "added_at": datetime.utcnow()})
            user_states.pop(user_id, None)
            await event.respond(fancy(f"✅ **Admin Added:** {name_} (`{new_id}`)"),
                                buttons=[[color_btn("◀️ Manage Admins", "manage_admins", "default")]])
            try:
                await bot.send_message(new_id, fancy("🔑 You have been granted **Admin Access** To the Bot!"))
            except Exception:
                pass
        except ValueError:
            await event.respond(fancy("❌ Invalid Telegram ID."))

# ─── 21. (removed duplicate deposit_paid handler — already handled by the
#          global CallbackQuery router above; a second registration here
#          was firing callback_router() twice per tap, causing errors) ──

# ─── 22. COMMANDS ──────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern="/help"))
async def cmd_help(event):
    await event.respond(
        fancy("❓ **Help center**\n\nchoose a topic below:"),
        buttons=[
            [color_btn("📖 How to Use", "help_howto", "default")],
            [color_btn("🔑 OTP Help", "help_otp", "default")],
            [color_btn("💳 Payment Help", "help_payment", "default")],
            [color_btn("🛡️ Why Trust Us?", "help_trust", "default")],
            [color_btn("🏠 Home", "main_menu", "default")],
        ])

@bot.on(events.NewMessage(pattern="/ping"))
async def cmd_ping(event):
    await event.respond(fancy("🏓 **Pong!**\nBot is alive and running."))

@bot.on(events.NewMessage(pattern="/cancel"))
async def cmd_cancel(event):
    user_states.pop(event.sender_id, None)
    await event.respond(fancy("✅ Current Action Cancelled."),
                        buttons=[[color_btn("🏠 Home", "main_menu", "default")]])

@bot.on(events.NewMessage(pattern="/info"))
async def cmd_info(event):
    args = event.message.text.split()
    if len(args) < 2:
        await event.respond(fancy("❌ Usage: `/info <User_ID or Order_ID>`"))
        return
    target = args[1]
    try:
        uid = int(target)
        user = await users_col.find_one({"user_id": uid})
        if user:
            orders = await orders_col.count_documents({"user_id": uid})
            deps = await deposits_col.count_documents({"user_id": uid})
            await event.respond(fancy(f"👤 **User Info**\n\n• ID: `{uid}`\n• Balance: `₹{user.get('balance',0):.2f}`\n• Orders: `{orders}`\n• Deposits: `{deps}`"))
            return
    except ValueError:
        pass
    order = await orders_col.find_one({"_id": target})
    if order:
        await event.respond(fancy(f"📋 **Order Info**\n\n• ID: `{target}`\n• User: `{order.get('user_id')}`\n• Country: {order.get('country_flag','')} {order.get('country')}\n• Phone: `{order.get('phone')}`\n• Status: `{order.get('status')}`"))
    else:
        await event.respond(fancy("❌ No user or order found."))

@bot.on(events.NewMessage(pattern="/request"))
async def cmd_request(event):
    args = event.message.text.split()
    if len(args) < 2:
        await event.respond(fancy("❌ Usage: `/request <Country_Code>`"))
        return
    cc = args[1].upper()
    for admin_id in await get_all_admin_ids():
        try:
            await bot.send_message(admin_id, fancy(f"📢 **Request for restock**\n\nuser `{event.sender_id}` requests `{cc}`."))
        except Exception:
            pass
    await event.respond(fancy(f"✅ Request for `{cc}` sent to admins."))

@bot.on(events.NewMessage(pattern="/feedback"))
async def cmd_feedback(event):
    args = event.message.text.split(maxsplit=1)
    if len(args) < 2:
        await event.respond(fancy("❌ Please provide your feedback after the command."))
        return
    feedback = args[1]
    for admin_id in await get_all_admin_ids():
        try:
            await bot.send_message(admin_id, fancy(f"💬 **New Feedback**\n\nUser `{event.sender_id}`:\n{feedback}"))
        except Exception:
            pass
    await event.respond(fancy("✅ Thank you for your feedback!"))

# ─── 23. SELF‑PING (only needed on hosts that sleep an idle web
#          service, like Render's free tier; harmless no-op on AWS
#          EC2/ECS/App Runner where the process just keeps running) ──
async def self_ping():
    while True:
        await asyncio.sleep(240)
        url = RENDER_EXTERNAL_URL
        if not url:
            continue
        try:
            import aiohttp
            async with aiohttp.ClientSession() as session:
                await session.get(f"{url}/ping", timeout=10)
                log.info("[self-ping] Ping sent to keep bot awake.")
        except Exception as e:
            log.warning(f"[self-ping] Failed: {e}")

# ─── 24. HEALTH‑CHECK WEB SERVER ──────────────────────────────
import threading
import uvicorn
from fastapi import FastAPI, Request
from fastapi.responses import JSONResponse

_web = FastAPI(title="Prime Vault", docs_url="/docs")

@_web.get("/", response_class=JSONResponse)
async def health():
    return {"status": "ok", "bot": "Prime Vault is running"}

@_web.get("/ping")
async def ping():
    return {"pong": True}

# ─── 24b. UPI APP REDIRECT (opens the phone's UPI app) ──────────
from fastapi.responses import HTMLResponse
import json as _json

@_web.get("/pay/{token}")
async def pay_redirect(token: str):
    doc = await db["pay_links"].find_one({"token": token})
    if not doc or not str(doc.get("link", "")).startswith("upi://"):
        return HTMLResponse("<h3 style='font-family:sans-serif;text-align:center;margin-top:40px'>"
                            "Link expired. Go back to the bot and try again.</h3>", status_code=404)
    link = doc["link"]
    js_link = _json.dumps(link).replace("</", "<\\/")
    page = (
        "<!doctype html><meta charset='utf-8'><meta name='viewport' content='width=device-width,initial-scale=1'>"
        "<title>Pay</title><body style='font-family:sans-serif;text-align:center;padding:40px'>"
        "<h3>Opening your UPI app…</h3><p>If nothing happens, tap the button:</p>"
        f"<p><a href='{_html.escape(link, quote=True)}' style='display:inline-block;padding:14px 26px;"
        "background:#2e7d32;color:#fff;border-radius:10px;text-decoration:none;font-size:18px'>Open UPI App</a></p>"
        f"<script>setTimeout(function(){{location.href={js_link};}},300);</script></body>"
    )
    return HTMLResponse(page)

# ─── 25. RAZORPAY WEBHOOK (real, signature-verified) ────────────
@_web.post("/razorpay-webhook")
async def razorpay_webhook(request: Request):
    if not RAZORPAY_ENABLE_WEBHOOK:
        return {"status": "webhook disabled — API polling is used"}
    raw_body = await request.body()
    signature = request.headers.get("X-Razorpay-Signature", "")

    if not RAZORPAY_WEBHOOK_SECRET or not signature:
        log.warning("[Razorpay webhook] rejected — webhook secret not configured or no signature header")
        return {"status": "webhook not configured"}

    expected = hmac.new(RAZORPAY_WEBHOOK_SECRET.encode(), raw_body, hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, signature):
        log.warning("[Razorpay webhook] rejected — signature mismatch")
        return {"status": "invalid signature"}

    try:
        body = json.loads(raw_body)
    except Exception:
        return {"status": "bad json"}

    event_name = body.get("event")

    if event_name == "qr_code.credited":
        try:
            qr_entity = body["payload"]["qr_code"]["entity"]
            payment_entity = body["payload"]["payment"]["entity"]
        except (KeyError, TypeError):
            return {"status": "ignored"}

        qr_id = qr_entity.get("id")
        paid_amount = payment_entity.get("amount", 0) / 100  # paise -> rupees
        dep = await deposits_col.find_one({"qr_code_id": qr_id, "status": "pending"})
        if not dep:
            log.warning(f"[Razorpay webhook] no pending deposit for qr_code_id={qr_id}")
            return {"status": "no matching deposit"}
        if round(paid_amount, 2) != round(dep.get("amount", 0), 2):
            log.warning(f"[Razorpay webhook] amount mismatch for {qr_id}: paid {paid_amount} vs expected {dep.get('amount')}")
            await log_event(f"⚠️ **Amount mismatch** on QR `{qr_id}` — paid ₹{paid_amount}, expected ₹{dep.get('amount')}. not auto-credited.")
            return {"status": "amount mismatch — manual review needed"}
        await _credit_deposit_by_id(dep["_id"])
        return {"status": "approved"}

    return {"status": "ok"}

def _start_health_server() -> None:
    port = int(os.getenv("PORT", 8080))
    log.info(f"[health] FastAPI listening on port {port}")
    uvicorn.run(_web, host="0.0.0.0", port=port, log_level="warning")

# ─── 25b. AUTO-VERIFY POLLER ────────────────────────────────────
async def deposit_poller():
    """Checks open Razorpay QR / Payment-Link deposits through the API and credits the
    verified ones — no webhook, domain or SSL needed, and the user never has to tap anything."""
    while True:
        await asyncio.sleep(RAZORPAY_API_POLL_SECONDS)
        if not (RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET):
            continue
        try:
            since = datetime.utcnow() - timedelta(minutes=35)
            async for dep in deposits_col.find(
                {"method": {"$in": ["razorpay_auto", "razorpay_link"]}, "status": "pending",
                 "created_at": {"$gte": since}}
            ).limit(50):
                pid = await razorpay_deposit_paid(dep)
                if pid:
                    await _credit_deposit_by_id(dep["_id"], payment_id=pid)
                await asyncio.sleep(0.2)
        except Exception as e:
            log.warning(f"[poller] {e}")

# <<EXT-BEGIN>>
# ═══════════════════════════════════════════════════════════════════
# ─── 27. EXTENDED FEATURES (ported from the OTP panel) ─────────────
# Server 3 · Bulk Buy · Stock announcements · Referral rewards ·
# Payment control · Session safety · Admin settings & log channels ·
# Upload (phone-login / session string / files) · OTP receiver
# ═══════════════════════════════════════════════════════════════════
SERVER3_NUMBER = 3     # Server 1 = own stock, Server 2 = VNH, Server 3 = Heart TG Store

# ── 27.1 shared helpers ─────────────────────────────────────────────
def _pb(text, data, style=None):
    """Button.inline look-alike used by the ported code → Vault's coloured button helper."""
    if isinstance(data, bytes):
        data = data.decode()
    plain = re.sub(r"[^a-z ]", "", str(text).lower()).strip()
    if style in ("success", "danger!", "primary"):
        pass                                   # explicit colour from the table screens
    elif plain.startswith(("next", "prev", "search", "new search", "all")):
        style = "primary"
    else:
        style = "default"                      # Back → blue, Home/Main Menu → red (see _mk_btn)
    return color_btn(text, data, style)

def _pu(text, url, style=None):
    return url_btn(text, url, "success")        # channel post buttons are green

async def safe_callback_answer(event, *args, **kwargs):
    """Answer a callback; expired / transient Telegram errors are ignored."""
    try:
        return await event.answer(*args, **kwargs)
    except Exception as exc:
        name = type(exc).__name__
        if name in ("QueryIdInvalidError", "ServerError", "RpcCallFailError", "TimedOutError"):
            return None
        raise

user_nav_context: Dict[int, dict] = {}
_s3_search_cache: Dict[tuple, dict] = {}     # (user_id, "p1"/"p2") -> {"query", "matches"}  (kept after opening a result)
server3_menu_cache: Dict[int, dict] = {}
server3_monitor_tasks: Dict[str, asyncio.Task] = {}

server3_server = Server3Server(
    api_key=SERVER3_API_KEY,
    base_url=SERVER3_API_BASE,
    settings_col=settings_col,
    get_usd_inr=get_usd_inr,
    now_ist=now_ist,
    default_markup_percent=SERVER3_MARKUP_PERCENT,
)

async def get_display_name(user_id: int) -> str:
    """'Name (@username)' for logs, falling back to the raw ID."""
    try:
        entity = await bot.get_entity(user_id)
        name = getattr(entity, "first_name", None) or "Unknown"
        if getattr(entity, "username", None):
            return f"{name} (@{entity.username})"
        return name
    except Exception:
        return str(user_id)

def format_telegram_name(user) -> str:
    if not user:
        return "Unknown"
    first = str(getattr(user, "first_name", "") or "").strip()
    last = str(getattr(user, "last_name", "") or "").strip()
    name = " ".join(x for x in (first, last) if x).strip()
    if name:
        return name
    username = str(getattr(user, "username", "") or "").strip()
    return f"@{username}" if username else "Unknown"

def mask_user_id(user_id) -> str:
    raw = str(user_id or "")
    if not raw:
        return "N/A"
    if len(raw) <= 4:
        return raw[:1] + "*" * max(1, len(raw) - 1)
    left = max(2, len(raw) // 3)
    right = max(1, len(raw) // 4)
    return raw[:left] + "*" * max(1, len(raw) - left - right) + raw[-right:]

def mask_public_phone(phone) -> str:
    raw = str(phone or "")
    if not raw or raw == "N/A":
        return "N/A"
    if len(raw) <= 6:
        return raw[:2] + "*" * max(1, len(raw) - 3) + raw[-1:]
    left = max(2, len(raw) // 4)
    right = max(2, len(raw) // 4)
    return raw[:left] + "*" * max(1, len(raw) - left - right) + raw[-right:]

async def _public_log_channel() -> int:
    if PUBLIC_LOG_CHANNEL_ID:
        return PUBLIC_LOG_CHANNEL_ID
    try:
        return int(await get_setting("public_log_channel_id", 0) or 0)
    except (TypeError, ValueError):
        return 0

async def _announcement_channel() -> int:
    try:
        v = int(await get_setting("announcement_channel_id", 0) or 0)
    except (TypeError, ValueError):
        v = 0
    return v or ANNOUNCEMENT_CHANNEL_ID or await _public_log_channel()

async def _payment_group() -> int:
    try:
        v = int(await get_setting("payment_group_id", 0) or 0)
    except (TypeError, ValueError):
        v = 0
    if v:
        return v
    if PAYMENT_GROUP_ID:
        return PAYMENT_GROUP_ID
    try:
        return LOGS_CHANNEL_ID or int(await get_setting("logs_channel_id", 0) or 0)
    except (TypeError, ValueError):
        return 0

async def public_log_event(text: str):
    """Privacy-safe public activity feed (masked IDs / numbers)."""
    channel = await _public_log_channel()
    if not channel:
        return
    try:
        uname = await get_bot_username()
        await bot.send_message(channel, fancy(text.rstrip()) + (f"\n\n🤖 **Bot:** @{uname}" if uname else ""),
                               buttons=[[url_btn("Buy Now", f"https://t.me/{uname}", "primary")]] if uname else None)
    except Exception as e:
        log.error(f"Failed to send public log: {e}")

async def show_insufficient_balance(event, required=None, back_data=b"store", back_label="Back"):
    """Replace the purchase screen with a direct Add-Funds action."""
    if isinstance(back_data, bytes):
        back_data = back_data.decode()
    req = f"\nRequired: `₹{required}`" if required is not None else ""
    await event.edit(
        fancy(
            "⚠️ **Insufficient funds**\n\n"
            "Your wallet balance is not enough to complete this purchase."
            f"{req}\n\n"
            "Please add funds and then try the purchase again."
        ),
        buttons=[
            [color_btn("Add Funds", "deposit", "default")],
            [color_btn(back_label, back_data, "default")],
        ],
    )
    await safe_callback_answer(event, "Insufficient balance.", alert=True)

async def notify_otp_sent_to_owner(*, buyer_id, phone, otp, server_name, country="N/A",
                                   is_refresh=False, received_at=None):
    """Admin/log notice after an OTP was really delivered to the buyer. Also
    advances a Direct-OTP bulk queue after the first OTP of the current number."""
    try:
        buyer_name = await get_display_name(int(buyer_id))
    except Exception:
        buyer_name = str(buyer_id)
    refresh_line = " (Refresh/Re-request)" if is_refresh else ""
    text = (
        f"✅ **OTP Sent to Buyer{refresh_line}**\n\n"
        f"• Server: `{server_name}`\n"
        f"• Buyer: {buyer_name}\n"
        f"• User ID: `{buyer_id}`\n"
        f"• Country: {country}\n"
        f"• Number: `{phone}`\n"
        f"• OTP: `{otp}`\n"
        f"• Time: `{received_at or now_ist().strftime('%d/%m/%Y %I:%M:%S %p')} IST`"
    )
    for admin_id in await get_all_admin_ids():
        try:
            await bot.send_message(admin_id, fancy(text))
        except Exception as e:
            log.error(f"Failed OTP notification to admin {admin_id}: {e}")
    if server_name == "Server 1" and not is_refresh:
        try:
            await advance_server1_bulk_after_otp(buyer_id=int(buyer_id), phone=str(phone))
        except Exception as e:
            log.exception(f"Could not advance bulk OTP queue for {buyer_id} / {phone}: {e}")


# ── 27.2 SERVER 3 (Heart TG Store API → Provider 1 / Provider 2) ────
def _server3_trim_label(value: str, limit: int = 24) -> str:
    value = str(value or "").strip()
    return value if len(value) <= limit else value[: limit - 1] + "…"

def _server3_display_label(row: dict) -> str:
    flag = str(row.get("flag") or "").strip()
    label = str(
        row.get("label")
        or row.get("country_name")
        or row.get("country")
        or row.get("key")
        or "Unknown"
    ).strip()
    return f"{flag} {label}".strip()

async def _server3_stock_row_price(row: dict) -> float | None:
    try:
        base_inr = row.get("base_inr")
        if base_inr is not None:
            return (await server3_server.calculate_price_inr(float(base_inr)))["retail_inr"]
        base_price = row.get("base_price")
        if base_price is not None:
            return (await server3_server.calculate_price_usd(float(base_price)))["retail_inr"]
    except Exception:
        pass
    return None

async def _server3_sort_provider1_items(items: list[dict]) -> list[dict]:
    """Sort Provider 1 stock by the customer's final bot price, low -> high."""
    priced = []
    for row in items:
        retail = await _server3_stock_row_price(row)
        priced.append((float(retail) if retail is not None else float("inf"), _server3_display_label(row).casefold(), row))
    priced.sort(key=lambda x: (x[0], x[1]))
    return [row for _, _, row in priced]

def _server3_provider1_matches(items: list[dict], query: str) -> list[dict]:
    q = str(query or "").strip().casefold()
    if not q:
        return []
    matches = []
    for row in items:
        haystack = " ".join(
            str(row.get(k) or "")
            for k in ("label", "country_name", "country", "key")
        ).casefold()
        if q in haystack:
            matches.append(row)
    return matches

def _server3_provider2_matches(items: list[dict], query: str) -> list[dict]:
    q = str(query or "").strip().casefold()
    if not q:
        return []
    matches = []
    for row in items:
        haystack = " ".join(
            str(row.get(k) or "")
            for k in ("label", "country_name", "country", "key")
        ).casefold()
        if q in haystack:
            matches.append(row)
    return matches

def _s3_btn_label(row: dict, price_txt=None) -> str:
    flag = str(row.get("flag") or "").strip()
    name = str(row.get("label") or row.get("country_name") or row.get("country") or row.get("key") or "Unknown").strip()
    text = _fl(flag) + fancy_btn(_server3_trim_label(name, 28))
    return text + (f" ¦ ₹{price_txt}" if price_txt is not None else "")

_p1_list_back: Dict[int, str] = {}

async def _build_server3_provider1_rows(items: list[dict], start_index: int):
    btn_items = []
    page_lines = []
    for offset, item in enumerate(items):
        idx = start_index + offset
        retail = await _server3_stock_row_price(item)
        price_text = f"₹{retail:g}" if isinstance(retail, (int, float)) else (f"₹{retail}" if retail is not None else "--")
        qty = int(item.get("quantity", 0) or 0)
        cb = f"server3_p1_stock_{idx}_0".encode()
        label = _server3_display_label(item)
        short = f"{retail:g}" if isinstance(retail, (int, float)) else "--"
        btn_items.append((_s3_btn_label(item, short), cb))
        page_lines.append(f"{offset + 1}. {label} — {price_text} — Stock: {qty}")
    return _pack_btns(btn_items, short_len=22), page_lines

def _build_server3_provider2_grid(chunk: list[dict]):
    items = []
    for row in chunk:
        code = str(row.get("country") or "").upper()
        if not code:
            continue
        items.append((_s3_btn_label(row), f"server3_p2_country_{code}".encode()))
    return _pack_btns(items, short_len=17)

async def build_server3_provider1_menu(user_id: int, page: int = 0):
    items = await server3_server.provider1_stock()
    if not items:
        return None, None

    # Always show Provider 1 from cheapest to most expensive using our bot price.
    items = await _server3_sort_provider1_items(items)
    server3_menu_cache.setdefault(user_id, {})["p1_items"] = items

    per_page = 8
    total_pages = max(1, (len(items) + per_page - 1) // per_page)
    page = max(0, min(page, total_pages - 1))
    start = page * per_page
    chunk = items[start:start + per_page]

    buttons, page_lines = await _build_server3_provider1_rows(chunk, start)

    if total_pages > 1:
        buttons.append(_page_row(page, total_pages, lambda i: f"server3_p1_page_{i}".encode(), b"server3_noop", style="danger"))

    _back = styled_btn("← " + fancy_btn("Providers"), b"server3", STYLE_GREEN)
    if total_pages > 1:
        buttons.append([_back, styled_btn(fancy_btn("Search"), b"server3_p1_search_country", STYLE_GREEN)])
    else:
        buttons.append([_back])

    details_text = "\n".join(page_lines) if page_lines else "No items on this page."
    text_msg = PLAIN + (
        "🛰️ **Server 3 — Provider 1**\n\n"
        "Choose an account category.\n"
        "💰 Sorted by price: **Low → High**\n"
        f"📄 Page {page+1}/{total_pages}\n\n"
        f"{details_text}"
    )
    return text_msg, buttons

async def build_server3_provider1_search_results(user_id: int, page: int = 0):
    state = user_states.get(user_id, {})
    if state.get("action") != "server3_p1_search_results" or not state.get("matches"):
        state = _s3_search_cache.get((user_id, "p1"), {})
    query = str(state.get("query", "")).strip()
    items = list(state.get("matches") or [])
    if not items:
        return None, None

    # Search results retain the same low -> high price ordering.
    items = await _server3_sort_provider1_items(items)
    server3_menu_cache.setdefault(user_id, {})["p1_items"] = items

    per_page = 8
    total_pages = max(1, (len(items) + per_page - 1) // per_page)
    page = max(0, min(page, total_pages - 1))
    start = page * per_page
    chunk = items[start:start + per_page]

    buttons, page_lines = await _build_server3_provider1_rows(chunk, start)

    if total_pages > 1:
        buttons.append(_page_row(page, total_pages, lambda i: f"server3_p1_search_page_{i}".encode(), b"server3_noop", style="danger"))

    buttons.append([
        _pb("🔎 New Search", b"server3_p1_search_country", style="success"),
        _pb("📋 All", b"server3_p1", style="success"),
    ])
    buttons.append([styled_btn("← " + fancy_btn("Providers"), b"server3", STYLE_GREEN)])

    details_text = "\n".join(page_lines) if page_lines else "No items on this page."
    text_msg = (
        f"🔎 **Provider 1 Search** — `{query}`\n\n"
        "💰 Sorted by price: **Low → High**\n"
        f"📄 Page {page+1}/{total_pages}\n\n"
        f"{details_text}"
    )
    return text_msg, buttons

async def build_server3_provider2_menu(user_id: int, page: int = 0):
    countries = await server3_server.provider2_countries()
    if not countries:
        return None, None

    # Alphabetical list makes the full list predictable; search is available below.
    countries = sorted(
        countries,
        key=lambda row: (
            str(row.get("country_name") or row.get("label") or row.get("country") or "").casefold(),
            str(row.get("country") or "").casefold(),
        ),
    )
    server3_menu_cache.setdefault(user_id, {})["p2_countries"] = countries

    per_page = 18
    total_pages = max(1, (len(countries) + per_page - 1) // per_page)
    page = max(0, min(page, total_pages - 1))
    chunk = countries[page * per_page:(page + 1) * per_page]

    buttons = _build_server3_provider2_grid(chunk)

    if total_pages > 1:
        buttons.append(_page_row(page, total_pages, lambda i: f"server3_p2_page_{i}".encode(), b"server3_noop", style="danger"))

    _back = styled_btn("← " + fancy_btn("Providers"), b"server3", STYLE_GREEN)
    if total_pages > 1:
        buttons.append([_back, styled_btn(fancy_btn("Search"), b"server3_p2_search_country", STYLE_GREEN)])
    else:
        buttons.append([_back])

    text_msg = PLAIN + (
        "🛰️ **Server 3 — Provider 2**\n\n"
        "Choose a country. Live price is checked after you select it.\n"
        "📋 Two-column country list\n"
        f"Page {page+1}/{total_pages}"
    )
    return text_msg, buttons

async def build_server3_provider2_search_results(user_id: int, page: int = 0):
    state = user_states.get(user_id, {})
    if state.get("action") != "server3_p2_search_results" or not state.get("matches"):
        state = _s3_search_cache.get((user_id, "p2"), {})
    query = str(state.get("query", "")).strip()
    countries = list(state.get("matches") or [])
    if not countries:
        return None, None

    countries = sorted(
        countries,
        key=lambda row: (
            str(row.get("country_name") or row.get("label") or row.get("country") or "").casefold(),
            str(row.get("country") or "").casefold(),
        ),
    )
    server3_menu_cache.setdefault(user_id, {})["p2_countries"] = countries

    per_page = 18
    total_pages = max(1, (len(countries) + per_page - 1) // per_page)
    page = max(0, min(page, total_pages - 1))
    chunk = countries[page * per_page:(page + 1) * per_page]

    buttons = _build_server3_provider2_grid(chunk)

    if total_pages > 1:
        buttons.append(_page_row(page, total_pages, lambda i: f"server3_p2_search_page_{i}".encode(), b"server3_noop", style="danger"))

    buttons.append([
        _pb("🔎 New Search", b"server3_p2_search_country", style="success"),
        _pb("📋 All Countries", b"server3_p2", style="success"),
    ])
    buttons.append([styled_btn("← " + fancy_btn("Providers"), b"server3", STYLE_GREEN)])

    text_msg = (
        f"🔎 **Provider 2 Search** — `{query}`\n\n"
        "Choose a country to continue.\n"
        "📋 Two-column country list\n"
        f"Page {page+1}/{total_pages}"
    )
    return text_msg, buttons

async def _server3_restore_preorder_money(
    user_id: int,
    retail_price: float,
    withdrawable_deducted: float,
    finance_reservation: dict | None,
    reason: str,
):
    update = {"$inc": {"balance": float(retail_price)}}
    if withdrawable_deducted > 0:
        update["$inc"]["withdrawable"] = float(withdrawable_deducted)
    await users_col.update_one({"user_id": int(user_id)}, update)

async def _server3_refund_committed_order(order: dict, reason: str) -> bool:
    """Refund customer exactly once after the supplier confirms an order refund."""
    if not order or not order.get("_id"):
        return False
    result = await orders_col.update_one(
        {
            "_id": order["_id"],
            "customer_refunded": {"$ne": True},
        },
        {
            "$set": {
                "customer_refunded": True,
                "customer_refunded_at": now_ist(),
                "refund_reason": str(reason or "supplier_refund"),
                "status": "refunded",
            }
        },
    )
    if result.modified_count == 0:
        return False

    amount = float(order.get("amount", 0) or 0)
    withdrawable_refund = float(order.get("withdrawable_deducted", 0) or 0)
    inc = {"balance": amount}
    if withdrawable_refund > 0:
        inc["withdrawable"] = withdrawable_refund
    await users_col.update_one({"user_id": int(order["user_id"])}, {"$inc": inc})

    try:
        await log_event(
            "💸 **Server 3 Order Refunded**\n"
            f"👤 User: `{order.get('user_id')}`\n"
            f"📱 Number: `{order.get('phone', 'N/A')}`\n"
            f"🛰️ Provider: **Provider {order.get('server3_provider', '?')}**\n"
            f"💰 Customer refund: **₹{amount}**\n"
            f"🧾 Reason: `{reason or 'supplier_refund'}`"
        )
    except Exception:
        pass
    return True

async def _server3_get_order(local_order_id: str, user_id: int):
    try:
        oid = ObjectId(str(local_order_id))
    except Exception:
        return None
    order = await orders_col.find_one({"_id": oid})
    if not order:
        return None
    if str(order.get("user_id")) != str(user_id):
        return None
    if order.get("source") != "server3":
        return None
    return order

async def _server3_show_refund(event, order: dict, reason: str):
    refunded_now = await _server3_refund_committed_order(order, reason)
    amount = float(order.get("amount", 0) or 0)
    suffix = (
        f"\n\n₹{amount} has been returned to your bot balance."
        if refunded_now or order.get("customer_refunded")
        else ""
    )
    await event.edit(
        "❌ **OTP could not be completed.**\n\n"
        "This order was refunded." + suffix,
        buttons=[[_pb("🔙 Main Menu", b"main_menu", style="primary")]],
    )

async def _server3_deliver_otp(event, order: dict, local_order_id: str, status_data: dict):
    otp = str(status_data.get("otp") or "").strip()
    if not otp:
        return False

    twofa = str(status_data.get("twofa") or order.get("twofa") or "").strip()
    old_count = int(order.get("otp_received_count", 0) or 0)
    await orders_col.update_one(
        {"_id": order["_id"]},
        {
            "$set": {
                "status": "otp_received",
                "otp_received_at": now_ist(),
                "last_otp": otp,
                "twofa": twofa or None,
            },
            "$inc": {"otp_received_count": 1},
        },
    )

    msg = (
        "✅ **OTP Received**\n\n"
        f"📱 Number: `{order.get('phone', '')}`\n"
        f"🔐 OTP: `{otp}`"
    )
    if twofa:
        msg += f"\n🔒 2FA: `{twofa}`"
    msg += "\n\nKeep these details private."

    await event.edit(
        msg,
        buttons=[
            [_pb("🔄 Request New OTP", f"server3_restartotp_{local_order_id}".encode(), style="primary")],
            [_pb("🔙 Main Menu", b"main_menu", style="primary")],
        ],
    )

    try:
        await notify_otp_sent_to_owner(
            buyer_id=order["user_id"],
            phone=order.get("phone", ""),
            otp=otp,
            server_name=f"Server 3 / Provider {order.get('server3_provider', '?')}",
            country=order.get("country", "N/A"),
            is_refresh=old_count > 0,
        )
    except Exception as exc:
        logging.error("Server 3 owner OTP notification failed: %s", exc)
    return True

class _Server3MessageEditor:
    def __init__(self, client, chat_id, message_id):
        self.client = client
        self.chat_id = chat_id
        self.message_id = message_id

    async def edit(self, text, buttons=None):
        try:
            return await self.client.edit_message(
                self.chat_id,
                self.message_id,
                text,
                buttons=buttons,
            )
        except MessageNotModifiedError:
            return None

async def _server3_background_monitor(local_order_id: str, user_id: int, client, chat_id, message_id):
    key = str(local_order_id)
    editor = _Server3MessageEditor(client, chat_id, message_id)
    try:
        listener_false_count = 0
        # Provider 1's first refundable window is 5 minutes. Monitor slightly
        # beyond it so a supplier-side automatic refund is mirrored to the
        # customer's bot balance without requiring another button press.
        for _ in range(75):
            order = await _server3_get_order(local_order_id, user_id)
            if not order:
                return
            if order.get("status") in {"otp_received", "refunded"}:
                return

            response = await server3_server.order_status(str(order.get("provider_order_id") or ""))
            if not server3_server.ok(response):
                code = server3_server.code(response)
                if code == "ORDER_REFUNDED":
                    await _server3_show_refund(editor, order, "order_refunded")
                    return
                delay = int(response.get("retry_after") or 5)
                await asyncio.sleep(max(5, min(delay, 15)))
                continue

            status = str(response.get("status") or "").lower()
            if status == "refunded":
                await _server3_show_refund(editor, order, str(response.get("reason") or "supplier_refund"))
                return
            if status == "delivered":
                if await _server3_deliver_otp(editor, order, local_order_id, response):
                    return
                await editor.edit(
                    "⚠️ **Order completed but no OTP was returned.**\n\nPlease contact admin.",
                    buttons=[[_pb("🔙 Main Menu", b"main_menu", style="primary")]],
                )
                return

            if status == "waiting" and int(order.get("server3_provider", 0) or 0) == 1:
                if response.get("window_ended") is True:
                    await editor.edit(
                        "⏳ **No OTP received yet.**\n\nTap below to request a new OTP window.",
                        buttons=[
                            [_pb("🔄 Request New OTP", f"server3_restartotp_{local_order_id}".encode(), style="primary")],
                            [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                        ],
                    )
                    return
                if response.get("listening") is False:
                    listener_false_count += 1
                    if listener_false_count >= 3:
                        await editor.edit(
                            "⏳ **OTP connection needs a retry.**\n\nTap below to continue waiting for a new code.",
                            buttons=[
                                [_pb("🔄 Retry OTP", f"server3_restartotp_{local_order_id}".encode(), style="primary")],
                                [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                            ],
                        )
                        return
                else:
                    listener_false_count = 0

            delay = int(response.get("retry_after") or 5)
            await asyncio.sleep(max(5, min(delay, 15)))

        await editor.edit(
            "⏳ **OTP is still pending.**\n\nTap below to check again.",
            buttons=[
                [_pb("🔄 Check OTP", f"server3_checkotp_{local_order_id}".encode(), style="primary")],
                [_pb("🔙 Main Menu", b"main_menu", style="primary")],
            ],
        )
    except Exception as exc:
        logging.error("Server 3 background monitor failed order=%s: %s", local_order_id, exc)
    finally:
        server3_monitor_tasks.pop(key, None)

def _server3_schedule_monitor(event, order: dict, local_order_id: str):
    try:
        key = str(local_order_id)
        existing = server3_monitor_tasks.get(key)
        if existing and not existing.done():
            return
        client = getattr(event, "client", None) or bot
        chat_id = getattr(event, "chat_id", None)
        message_id = getattr(event, "message_id", None)
        if message_id is None:
            message_id = getattr(getattr(event, "query", None), "msg_id", None)
        if chat_id is None:
            chat_id = getattr(getattr(event, "message", None), "chat_id", None)
        if not client or chat_id is None or message_id is None:
            return
        task = asyncio.create_task(
            _server3_background_monitor(
                local_order_id,
                int(order["user_id"]),
                client,
                chat_id,
                message_id,
            )
        )
        server3_monitor_tasks[key] = task
    except Exception as exc:
        logging.warning("Could not start Server 3 background monitor: %s", exc)

async def _server3_poll_order_status(event, order: dict, local_order_id: str, attempts: int = 6):
    provider_order_id = str(order.get("provider_order_id") or "")
    provider_no = int(order.get("server3_provider", 0) or 0)
    if not provider_order_id:
        await event.edit(
            "❌ **Order details are incomplete. Please contact admin.**",
            buttons=[[_pb("🔙 Main Menu", b"main_menu", style="primary")]],
        )
        return

    for attempt in range(max(1, attempts)):
        status_data = await server3_server.order_status(provider_order_id)
        if not server3_server.ok(status_data):
            code = server3_server.code(status_data)
            if code == "ORDER_REFUNDED":
                await _server3_show_refund(event, order, "order_refunded")
                return
            if code in server3_server.TEMPORARY_CODES or code in {"TIMEOUT", "CONNECTION_ERROR"}:
                if attempt + 1 < attempts:
                    delay = int(status_data.get("retry_after") or 5)
                    await asyncio.sleep(max(5, min(delay, 15)))
                    continue
                await event.edit(
                    "⏳ **Waiting for OTP...**\n\nPlease check again in a few seconds.",
                    buttons=[
                        [_pb("🔄 Check OTP", f"server3_checkotp_{local_order_id}".encode(), style="primary")],
                        [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                    ],
                )
                _server3_schedule_monitor(event, order, local_order_id)
                return

            logging.error(
                "Server 3 status failed local=%s provider_order=%s response=%r",
                local_order_id,
                provider_order_id,
                status_data,
            )
            await event.edit(
                "❌ **Could not check this order right now.**\n\nPlease contact admin if the issue continues.",
                buttons=[
                    [_pb("🔄 Try Again", f"server3_checkotp_{local_order_id}".encode(), style="primary")],
                    [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                ],
            )
            return

        status = str(status_data.get("status") or "").lower()
        if status == "refunded":
            await _server3_show_refund(event, order, str(status_data.get("reason") or "supplier_refund"))
            return

        if status == "delivered":
            if await _server3_deliver_otp(event, order, local_order_id, status_data):
                return
            await event.edit(
                "⚠️ **Order completed but no OTP was returned.**\n\nPlease contact admin.",
                buttons=[[_pb("🔙 Main Menu", b"main_menu", style="primary")]],
            )
            return

        if status == "ready":
            await event.edit(
                "📱 **Number is ready.**\n\nTap below when you are ready to request the login code.",
                buttons=[
                    [_pb("🔐 Get OTP", f"server3_startotp_{local_order_id}".encode(), style="success")],
                    [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                ],
            )
            return

        # Provider 1 exposes connection/window state. Never silently open a
        # second non-refundable OTP window when its first listener stops.
        if status == "waiting" and provider_no == 1:
            if status_data.get("window_ended") is True:
                await event.edit(
                    "⏳ **No OTP received yet.**\n\nTap below to request a new OTP window.",
                    buttons=[
                        [_pb("🔄 Request New OTP", f"server3_restartotp_{local_order_id}".encode(), style="primary")],
                        [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                    ],
                )
                return
            if status_data.get("listening") is False:
                # A listener can briefly report false while reconnecting. Give it
                # at least two status cycles before offering a new OTP window.
                if attempt < 2 and attempt + 1 < attempts:
                    await asyncio.sleep(5)
                    continue
                await event.edit(
                    "⏳ **OTP connection needs a retry.**\n\nTap below to continue waiting for a new code.",
                    buttons=[
                        [_pb("🔄 Retry OTP", f"server3_restartotp_{local_order_id}".encode(), style="primary")],
                        [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                    ],
                )
                return

        if attempt + 1 < attempts:
            delay = int(status_data.get("retry_after") or 5)
            await asyncio.sleep(max(5, min(delay, 15)))
            continue

        await event.edit(
            "⏳ **Waiting for OTP...**\n\nRequest the Telegram login code, then check again.",
            buttons=[
                [_pb("🔄 Check OTP", f"server3_checkotp_{local_order_id}".encode(), style="primary")],
                [_pb("🔙 Main Menu", b"main_menu", style="primary")],
            ],
        )
        _server3_schedule_monitor(event, order, local_order_id)
        return

async def _server3_start_otp(event, order: dict, local_order_id: str):
    provider_order_id = str(order.get("provider_order_id") or "")
    response = await server3_server.request_otp(provider_order_id)
    if not server3_server.ok(response):
        code = server3_server.code(response)
        if code == "ORDER_REFUNDED":
            await _server3_show_refund(event, order, "order_refunded")
            return
        if code in {"LISTENER_FAILED", "LISTENER_LIMIT", "SERVER_BUSY", "RATE_LIMIT_EXCEEDED", "TIMEOUT", "CONNECTION_ERROR"}:
            await event.edit(
                "⏳ **OTP request is temporarily unavailable.**\n\nPlease try again shortly.",
                buttons=[
                    [_pb("🔄 Retry OTP", f"server3_restartotp_{local_order_id}".encode(), style="primary")],
                    [_pb("🔙 Main Menu", b"main_menu", style="primary")],
                ],
            )
            return
        logging.error("Server 3 OTP request failed order=%s response=%r", provider_order_id, response)
        await event.edit(
            "❌ **Could not start OTP request.**\n\nPlease contact admin if the issue continues.",
            buttons=[
                [_pb("🔄 Try Again", f"server3_restartotp_{local_order_id}".encode(), style="primary")],
                [_pb("🔙 Main Menu", b"main_menu", style="primary")],
            ],
        )
        return

    await orders_col.update_one(
        {"_id": order["_id"]},
        {
            "$set": {
                "status": "waiting_otp",
                "last_otp_request_at": now_ist(),
                "otp_window_refundable": response.get("refundable"),
                "otp_window_seconds": response.get("window_seconds"),
            },
            "$inc": {"otp_request_count": 1},
        },
    )

    await event.edit(
        "⏳ **Waiting for OTP...**\n\nPlease request the Telegram login code now.",
        buttons=[[_pb("🔄 Check OTP", f"server3_checkotp_{local_order_id}".encode(), style="primary")]],
    )
    # Poll at the supplier-recommended cadence for a short foreground window.
    order = await _server3_get_order(local_order_id, int(order["user_id"])) or order
    await _server3_poll_order_status(event, order, local_order_id, attempts=6)

async def handle_server3_callback(event, data: str, user_id: int) -> bool:
    """Handle every Server 3 callback. Returns True when the callback belongs here."""
    if not data.startswith("server3"):
        return False

    if data == "server3_noop":
        await safe_callback_answer(event, "Select a row.", alert=False)
        return True

    if data == "server3":
        if not server3_server.configured:
            await safe_callback_answer(event, "❌ Server 3 is not configured.", alert=True)
            return True
        await event.edit(
            plain("🛰️ **Server 3**\n\nChoose a provider:\n\n"
                  "🔵 **Provider 1** — curated account categories with live stock\n"
                  "🟣 **Provider 2** — large country pool with live rates\n\n"
                  "Both providers deliver Telegram login numbers and OTPs."),
            buttons=[
                [plain_btn(fancy_btn("Provider 1"), b"server3_p1")],
                [plain_btn(fancy_btn("Provider 2"), b"server3_p2")],
                [blue_btn(fancy_btn("Servers"), b"store")],
            ],
        )
        await safe_callback_answer(event)
        return True

    if data == "server3_p1_search_country":
        if not server3_server.configured:
            await safe_callback_answer(event, "❌ Server 3 is not configured.", alert=True)
            return True
        user_states[user_id] = {
            "action": "server3_p1_search_country",
            "step": "await_query",
        }
        _arm_prompt(user_id, event)
        await event.edit(
            "🔎 **Provider 1 — Search Country**\n\n"
            "Send country name, country code, or account label.\n"
            "Examples: `India`, `IND`, `Colombia`",
            buttons=[
                [_pb("📋 Back to All", b"server3_p1", style="primary")],
                [_pb("🔙 Providers", b"server3", style="danger")],
            ],
        )
        await safe_callback_answer(event)
        return True

    if data.startswith("server3_p1_search_page_"):
        user_nav_context.setdefault(user_id, {})["server3_p1"] = data
        try:
            page = int(data.rsplit("_", 1)[1])
        except Exception:
            page = 0
        msg, buttons = await build_server3_provider1_search_results(user_id, page)
        if not buttons:
            await safe_callback_answer(event, "❌ Search results expired. Search again.", alert=True)
            return True
        await event.edit(msg, buttons=buttons)
        await safe_callback_answer(event)
        return True

    if data == "server3_p1":
        user_nav_context.setdefault(user_id, {})["server3_p1"] = "server3_p1"
        msg, buttons = await build_server3_provider1_menu(user_id, 0)
        if not buttons:
            await safe_callback_answer(event, "❌ Provider 1 is temporarily unavailable.", alert=True)
            return True
        await event.edit(msg, buttons=buttons)
        await safe_callback_answer(event)
        return True

    if data.startswith("server3_p1_page_"):
        user_nav_context.setdefault(user_id, {})["server3_p1"] = data
        try:
            page = int(data.rsplit("_", 1)[1])
        except Exception:
            page = 0
        msg, buttons = await build_server3_provider1_menu(user_id, page)
        if not buttons:
            await safe_callback_answer(event, "❌ Provider 1 is temporarily unavailable.", alert=True)
            return True
        await event.edit(msg, buttons=buttons)
        await safe_callback_answer(event)
        return True

    if data.startswith("server3_p1_stock_"):
        try:
            _p = data.split("_")
            idx, page = int(_p[3]), int(_p[4])
        except Exception:
            await safe_callback_answer(event, "Invalid selection.", alert=True)
            return True
        items = (server3_menu_cache.get(user_id) or {}).get("p1_items") or await server3_server.provider1_stock()
        if idx < 0 or idx >= len(items):
            await safe_callback_answer(event, "Selection expired. Open Provider 1 again.", alert=True)
            return True
        item = items[idx]
        qty = int(item.get("quantity", 0) or 0)
        if qty <= 0:
            await safe_callback_answer(event, "❌ Out of stock!", alert=True)
            return True
        ctx = user_nav_context.setdefault(user_id, {})
        cur = str(ctx.get("server3_p1", "server3_p1"))
        if not cur.startswith("server3_p1_stock_"):
            _p1_list_back[user_id] = cur
        per = 16
        pages = (qty - 1) // per + 1
        page = max(0, min(page, pages - 1))
        ctx["server3_p1"] = f"server3_p1_stock_{idx}_{page}"
        retail = await _server3_stock_row_price(item)
        ptxt = f"{retail:g}" if isinstance(retail, (int, float)) else "--"
        flag = str(item.get("flag") or "").strip()
        name = str(item.get("label") or item.get("country_name") or item.get("country") or "Stock").strip()
        raw_c = str(item.get("country") or "").strip()
        code = raw_c.upper() if (2 <= len(raw_c) <= 3 and raw_c.isalpha()) else (resolve_country(name.split(" ")[0]).get("code") or "")
        dial = ""
        if code:
            dd = await countries_col.find_one({"code": code[:2]}, {"dial": 1})
            dial = str((dd or {}).get("dial") or "").lstrip("+").strip()
        lab = f"{_fl(flag)}{code}{'+' + dial if dial else ''} ¦ ₹{ptxt}" if code else f"{_fl(flag)}{_server3_trim_label(name, 14)} ¦ ₹{ptxt}"
        cb = f"server3_p1_item_{idx}".encode()
        n = min(per, qty - page * per)
        rows = [[blue_btn(lab, cb) for _ in range(min(2, n - i))] for i in range(0, n, 2)]
        if pages > 1:
            rows.append(_page_row(page, pages, lambda i: f"server3_p1_stock_{idx}_{i}".encode(),
                                  f"server3_p1_stock_{idx}_{page}".encode(), style="danger"))
        rows.append([styled_btn("← " + fancy_btn("Back"), str(_p1_list_back.get(user_id) or "server3_p1").encode(), STYLE_GREEN)])
        await event.edit(
            RAW + f"{flag}  **{name.upper()}**\n{LINE}\n"
                  f"> Stock  :  **{qty:,}**\n> From   :  **₹{ptxt}**\n> Page   :  **{page + 1} of {pages}**",
            buttons=rows)
        await safe_callback_answer(event)
        return True

    if data.startswith("server3_p1_item_"):
        try:
            idx = int(data.rsplit("_", 1)[1])
        except Exception:
            await safe_callback_answer(event, "Invalid selection.", alert=True)
            return True
        items = (server3_menu_cache.get(user_id) or {}).get("p1_items") or await server3_server.provider1_stock()
        if idx < 0 or idx >= len(items):
            await safe_callback_answer(event, "Selection expired. Open Provider 1 again.", alert=True)
            return True
        item = items[idx]
        item_key = str(item.get("key") or "")
        preview = await server3_server.provider1_preview(item_key)
        if not server3_server.ok(preview) or preview.get("sufficient_balance") is False:
            code = server3_server.code(preview)

            if code in {"NO_DELIVERABLE_STOCK", "OUT_OF_STOCK"}:
                # /stock may still show quantity while the supplier's live Telegram
                # verification says there is no actually usable account. This is
                # expected stock churn, not an application error.
                server3_server.mark_provider1_unavailable(item_key, ttl_seconds=90)
                logging.info(
                    "Server 3 Provider 1 item temporarily hidden after live stock check: key=%s code=%s",
                    item_key,
                    code,
                )

                msg, buttons = await build_server3_provider1_menu(user_id, 0)
                if buttons:
                    await event.edit(
                        msg + "\n\n⚠️ The selected account just became unavailable. List refreshed.",
                        buttons=buttons,
                    )
                else:
                    await event.edit(
                        "❌ **Provider 1 stock is temporarily unavailable.**\n\n"
                        "Please try again in a moment.",
                        buttons=[[_pb("🔙 Providers", b"server3", style="primary")]],
                    )
                await safe_callback_answer(
                    event,
                    "Stock changed. List refreshed.",
                    alert=True,
                )
                return True

            logging.warning(
                "Server 3 Provider 1 preview failed key=%s code=%s response=%r",
                item_key,
                code,
                preview,
            )
            await safe_callback_answer(event, "❌ This account is temporarily unavailable.", alert=True)
            return True
        try:
            supplier_price = float(preview.get("would_charge"))
        except Exception:
            await safe_callback_answer(event, "❌ Live price unavailable.", alert=True)
            return True
        pricing = await server3_server.calculate_price_usd(supplier_price)
        label = str(item.get("label") or item.get("country_name") or item_key)
        country = str(item.get("country_name") or item.get("country") or label)
        user_states[user_id] = {
            "action": "server3_p1_confirmation",
            "item_key": item_key,
            "label": label,
            "country": country,
            "supplier_price": supplier_price,
            "wholesale_inr": pricing["wholesale_inr"],
            "retail_price": pricing["retail_inr"],
            "back_data": user_nav_context.get(user_id, {}).get("server3_p1", "server3_p1"),
        }
        await event.edit(
            "🔵 **Provider 1**\n\n"
            f"🌍 Account: **{label}**\n"
            f"📦 Available: **{int(preview.get('available', item.get('quantity', 0)) or 0)}**\n"
            f"💰 Price: **₹{pricing['retail_inr']}**\n\n"
            "After confirmation, a Telegram login number will be reserved for you.\n"
            "Proceed only when you are ready to use the number.",
            buttons=[
                [_pb("✅ Confirm Purchase", b"server3_p1_confirm", style="success")],
                [_pb(
                    "🔙 Back",
                    str(user_states[user_id].get("back_data") or "server3_p1").encode(),
                    style="primary",
                )],
            ],
        )
        await safe_callback_answer(event)
        return True

    if data == "server3_p1_confirm":
        state = user_states.get(user_id) or {}
        if state.get("action") != "server3_p1_confirmation":
            await safe_callback_answer(event, "Session expired. Please start again.", alert=True)
            return True

        quote = await server3_server.provider1_quote(state["item_key"])
        if not server3_server.ok(quote):
            logging.warning("Server 3 Provider 1 quote failed user=%s response=%r", user_id, quote)
            await safe_callback_answer(event, "❌ Account unavailable. Please refresh stock.", alert=True)
            return True
        q = quote.get("quote") or {}
        token = str(quote.get("confirm_token") or "")
        try:
            supplier_price = float(q.get("price"))
        except Exception:
            supplier_price = -1
        if not token or supplier_price < 0:
            logging.error("Server 3 Provider 1 bad quote: %r", quote)
            await safe_callback_answer(event, "❌ Could not prepare purchase.", alert=True)
            return True
        pricing = await server3_server.calculate_price_usd(supplier_price)
        retail_price = pricing["retail_inr"]
        wholesale_inr = pricing["wholesale_inr"]

        if abs(float(state.get("retail_price", 0)) - retail_price) > 0.01:
            state.update({
                "supplier_price": supplier_price,
                "wholesale_inr": wholesale_inr,
                "retail_price": retail_price,
            })
            user_states[user_id] = state
            await event.edit(
                "🔄 **Live price updated**\n\n"
                f"🌍 Account: **{state.get('label', state['item_key'])}**\n"
                f"💰 New Price: **₹{retail_price}**\n\n"
                "Tap confirm again if you want to continue at the updated price.",
                buttons=[
                    [_pb("✅ Confirm New Price", b"server3_p1_confirm", style="success")],
                    [_pb(
                    "🔙 Back",
                    str(user_states[user_id].get("back_data") or "server3_p1").encode(),
                    style="primary",
                )],
                ],
            )
            await safe_callback_answer(event, "Price refreshed.", alert=True)
            return True

        user = await users_col.find_one({"user_id": user_id})
        if not user or float(user.get("balance", 0) or 0) < retail_price:
            await show_insufficient_balance(
                event,
                required=retail_price,
                back_data=str(state.get("back_data") or "server3_p1").encode(),
                back_label="🔙 Back",
            )
            return True

        old_w = float(user.get("withdrawable", 0) or 0)
        withdrawable_deducted = min(old_w, retail_price)
        deducted = await users_col.update_one(
            {"user_id": user_id, "balance": {"$gte": retail_price}},
            {
                "$inc": {"balance": -retail_price},
                "$set": {"withdrawable": max(0.0, old_w - retail_price)},
            },
        )
        if deducted.modified_count == 0:
            await safe_callback_answer(event, "❌ Balance changed. Please try again.", alert=True)
            return True

        await safe_callback_answer(event, "Processing purchase...", alert=False)
        await event.edit("⏳ Reserving a number from Provider 1...")
        result = await server3_server.provider1_confirm(token)
        if not server3_server.ok(result):
            await _server3_restore_preorder_money(
                user_id, retail_price, withdrawable_deducted, None,
                f"provider1_{server3_server.code(result).lower() or 'failed'}",
            )
            logging.error("Server 3 Provider 1 confirm failed user=%s response=%r", user_id, result)
            user_states.pop(user_id, None)
            await event.edit(
                "❌ **Purchase could not be completed.**\n\n"
                f"₹{retail_price} has been returned to your bot balance. Please refresh and try again.",
                buttons=[[_pb("🔙 Provider 1", b"server3_p1", style="primary")]],
            )
            return True

        provider_order_id = str(result.get("order_id") or "").strip()
        data_obj = result.get("data") or {}
        phone = str(data_obj.get("phone") or "").strip()
        twofa = str(data_obj.get("twofa") or "").strip()
        charged = float(result.get("charged", supplier_price) or supplier_price)
        actual_pricing = await server3_server.calculate_price_usd(charged)
        # Provider confirmed at the quoted price. Store actual supplier cost for audit.
        incomplete = not provider_order_id or not phone
        inserted = await orders_col.insert_one({
            "user_id": user_id,
            "phone": phone or "N/A",
            "country": state.get("country") or state.get("label") or "N/A",
            "country_code": str(data_obj.get("country") or ""),
            "amount": retail_price,
            "wholesale_amount": actual_pricing["wholesale_inr"],
            "supplier_price": charged,
            "source": "server3",
            "server3_provider": 1,
            "provider_order_id": provider_order_id,
            "twofa": twofa or None,
            "withdrawable_deducted": withdrawable_deducted,
            "status": "provider_response_incomplete" if incomplete else str(result.get("otp_status") or "ready"),
            "created_at": now_ist(),
        })
        local_id = str(inserted.inserted_id)
        user_states.pop(user_id, None)

        if incomplete:
            logging.critical("Server 3 Provider 1 success but missing order/phone: %r", result)
            await event.edit(
                "⚠️ **Purchase needs admin review.**\n\n"
                "The provider accepted the order but returned incomplete delivery details. Please contact admin.",
                buttons=[[_pb("🔙 Main Menu", b"main_menu", style="primary")]],
            )
            return True

        await event.edit(
            "✅ **Number Reserved!**\n\n"
            f"🌍 Account: **{state.get('label', 'Provider 1')}**\n"
            f"📱 Number: `{phone}`\n"
            f"💰 Charged: **₹{retail_price}**\n\n"
            "Login to Telegram with this number, then tap **Get OTP**.",
            buttons=[
                [_pb("🔐 Get OTP", f"server3_startotp_{local_id}".encode(), style="success")],
                [_pb("🔙 Main Menu", b"main_menu", style="primary")],
            ],
        )
        try:
            buyer_name = await get_display_name(user_id)
            updated_user = await users_col.find_one({"user_id": user_id})
            new_balance = float((updated_user or {}).get("balance", 0) or 0)
            await log_event(
                "🛒 **New Account Purchase**\n"
                "🖥️ Server: **Server 3**\n"
                "🛰️ Provider: **Provider 1**\n"
                f"👤 Buyer: {buyer_name} (`{user_id}`)\n"
                f"📱 Phone: `{phone}`\n"
                f"🌍 Account: {state.get('label', 'N/A')}\n"
                f"💰 Retail: ₹{retail_price}\n"
                f"🧾 Supplier cost: ₹{actual_pricing['wholesale_inr']}\n"
                f"👛 Balance After: ₹{new_balance}\n"
                f"🕐 Time: {now_ist().strftime('%d/%m/%Y %H:%M:%S')} IST"
            )
            await public_log_event(
                "🛒 **New Purchase**\n"
                "🖥️ Server: **Server 3**\n"
                "🛰️ Provider: **Provider 1**\n"
                f"👤 User ID: `{mask_user_id(user_id)}`\n"
                f"📱 Number: `{mask_public_phone(phone)}`\n"
                f"💰 Amount: **₹{retail_price}**\n\n"
                "💙 **Thank you for your purchase!**"
            )
        except Exception:
            pass
        return True

    if data == "server3_p2_search_country":
        if not server3_server.configured:
            await safe_callback_answer(event, "❌ Server 3 is not configured.", alert=True)
            return True
        user_states[user_id] = {
            "action": "server3_p2_search_country",
            "step": "await_query",
        }
        _arm_prompt(user_id, event)
        await event.edit(
            "🔎 **Provider 2 — Search Country**\n\n"
            "Send country name or 2-letter country code.\n"
            "Examples: `India`, `IN`, `Bangladesh`, `BD`",
            buttons=[
                [_pb("📋 Back to All Countries", b"server3_p2", style="primary")],
                [_pb("🔙 Providers", b"server3", style="danger")],
            ],
        )
        await safe_callback_answer(event)
        return True

    if data.startswith("server3_p2_search_page_"):
        user_nav_context.setdefault(user_id, {})["server3_p2"] = data
        try:
            page = int(data.rsplit("_", 1)[1])
        except Exception:
            page = 0
        msg, buttons = await build_server3_provider2_search_results(user_id, page)
        if not buttons:
            await safe_callback_answer(event, "❌ Search results expired. Search again.", alert=True)
            return True
        await event.edit(msg, buttons=buttons)
        await safe_callback_answer(event)
        return True

    if data == "server3_p2":
        user_nav_context.setdefault(user_id, {})["server3_p2"] = "server3_p2"
        msg, buttons = await build_server3_provider2_menu(user_id, 0)
        if not buttons:
            await safe_callback_answer(event, "❌ Provider 2 is temporarily unavailable.", alert=True)
            return True
        await event.edit(msg, buttons=buttons)
        await safe_callback_answer(event)
        return True

    if data.startswith("server3_p2_page_"):
        user_nav_context.setdefault(user_id, {})["server3_p2"] = data
        try:
            page = int(data.rsplit("_", 1)[1])
        except Exception:
            page = 0
        msg, buttons = await build_server3_provider2_menu(user_id, page)
        if not buttons:
            await safe_callback_answer(event, "❌ Provider 2 is temporarily unavailable.", alert=True)
            return True
        await event.edit(msg, buttons=buttons)
        await safe_callback_answer(event)
        return True

    if data.startswith("server3_p2_country_"):
        country_code = data.split("server3_p2_country_", 1)[1].upper()
        countries = (server3_menu_cache.get(user_id) or {}).get("p2_countries") or await server3_server.provider2_countries()
        row = next((x for x in countries if str(x.get("country") or "").upper() == country_code), None)
        country_name = str((row or {}).get("country_name") or (row or {}).get("label") or country_code)
        preview = await server3_server.provider2_preview(country_code)
        if not server3_server.ok(preview) or preview.get("sufficient_balance") is False:
            logging.warning("Server 3 Provider 2 preview failed country=%s response=%r", country_code, preview)
            await safe_callback_answer(event, "❌ This country is temporarily unavailable.", alert=True)
            return True
        try:
            supplier_price = float(preview.get("would_charge"))
        except Exception:
            await safe_callback_answer(event, "❌ Live price unavailable.", alert=True)
            return True
        pricing = await server3_server.calculate_price_usd(supplier_price)
        user_states[user_id] = {
            "action": "server3_p2_confirmation",
            "country_code": country_code,
            "country": country_name,
            "supplier_price": supplier_price,
            "wholesale_inr": pricing["wholesale_inr"],
            "retail_price": pricing["retail_inr"],
            "back_data": user_nav_context.get(user_id, {}).get("server3_p2", "server3_p2"),
        }
        await event.edit(
            "🟣 **Provider 2**\n\n"
            f"🌍 Country: **{country_name} ({country_code})**\n"
            f"📦 Available: **{int(preview.get('available', 0) or 0)}**\n"
            f"💰 Price: **₹{pricing['retail_inr']}**\n\n"
            "Live stock can move quickly. Your bot will never accept a higher provider tier without a fresh confirmation.",
            buttons=[
                [_pb("✅ Confirm Purchase", b"server3_p2_confirm", style="success")],
                [_pb(
                    "🔙 Back",
                    str(user_states[user_id].get("back_data") or "server3_p2").encode(),
                    style="primary",
                )],
            ],
        )
        await safe_callback_answer(event)
        return True

    if data == "server3_p2_confirm":
        state = user_states.get(user_id) or {}
        if state.get("action") != "server3_p2_confirmation":
            await safe_callback_answer(event, "Session expired. Please start again.", alert=True)
            return True
        preview = await server3_server.provider2_preview(state["country_code"])
        if not server3_server.ok(preview) or preview.get("sufficient_balance") is False:
            await safe_callback_answer(event, "❌ Live stock unavailable. Please refresh.", alert=True)
            return True
        try:
            supplier_price = float(preview.get("would_charge"))
        except Exception:
            await safe_callback_answer(event, "❌ Live price unavailable.", alert=True)
            return True
        pricing = await server3_server.calculate_price_usd(supplier_price)
        retail_price = pricing["retail_inr"]
        wholesale_inr = pricing["wholesale_inr"]
        if abs(float(state.get("retail_price", 0)) - retail_price) > 0.01:
            state.update({
                "supplier_price": supplier_price,
                "wholesale_inr": wholesale_inr,
                "retail_price": retail_price,
            })
            user_states[user_id] = state
            await event.edit(
                "🔄 **Live price updated**\n\n"
                f"🌍 Country: **{state.get('country')} ({state.get('country_code')})**\n"
                f"💰 New Price: **₹{retail_price}**\n\n"
                "Tap confirm again if you want to continue at the updated price.",
                buttons=[
                    [_pb("✅ Confirm New Price", b"server3_p2_confirm", style="success")],
                    [_pb(
                    "🔙 Back",
                    str(user_states[user_id].get("back_data") or "server3_p2").encode(),
                    style="primary",
                )],
                ],
            )
            await safe_callback_answer(event, "Price refreshed.", alert=True)
            return True

        user = await users_col.find_one({"user_id": user_id})
        if not user or float(user.get("balance", 0) or 0) < retail_price:
            await show_insufficient_balance(
                event,
                required=retail_price,
                back_data=str(state.get("back_data") or "server3_p2").encode(),
                back_label="🔙 Back",
            )
            return True
        old_w = float(user.get("withdrawable", 0) or 0)
        withdrawable_deducted = min(old_w, retail_price)
        deducted = await users_col.update_one(
            {"user_id": user_id, "balance": {"$gte": retail_price}},
            {
                "$inc": {"balance": -retail_price},
                "$set": {"withdrawable": max(0.0, old_w - retail_price)},
            },
        )
        if deducted.modified_count == 0:
            await safe_callback_answer(event, "❌ Balance changed. Please try again.", alert=True)
            return True

        await safe_callback_answer(event, "Processing purchase...", alert=False)
        await event.edit("⏳ Reserving a number from Provider 2...")
        result = await server3_server.provider2_buy(state["country_code"], price=supplier_price)
        if not server3_server.ok(result):
            await _server3_restore_preorder_money(
                user_id, retail_price, withdrawable_deducted, None,
                f"provider2_{server3_server.code(result).lower() or 'failed'}",
            )
            logging.error("Server 3 Provider 2 purchase failed user=%s response=%r", user_id, result)
            user_states.pop(user_id, None)
            await event.edit(
                "❌ **Purchase could not be completed.**\n\n"
                f"₹{retail_price} has been returned to your bot balance. Please refresh and try again.",
                buttons=[[_pb("🔙 Provider 2", b"server3_p2", style="primary")]],
            )
            return True

        provider_order_id = str(result.get("order_id") or "").strip()
        data_obj = result.get("data") or {}
        phone = str(data_obj.get("phone") or "").strip()
        charged = float(result.get("charged", supplier_price) or supplier_price)
        actual_pricing = await server3_server.calculate_price_usd(charged)
        incomplete = not provider_order_id or not phone
        inserted = await orders_col.insert_one({
            "user_id": user_id,
            "phone": phone or "N/A",
            "country": state.get("country") or state.get("country_code"),
            "country_code": state.get("country_code"),
            "amount": retail_price,
            "wholesale_amount": actual_pricing["wholesale_inr"],
            "supplier_price": charged,
            "source": "server3",
            "server3_provider": 2,
            "provider_order_id": provider_order_id,
            "withdrawable_deducted": withdrawable_deducted,
            "status": "provider_response_incomplete" if incomplete else str(result.get("otp_status") or "waiting"),
            "created_at": now_ist(),
        })
        local_id = str(inserted.inserted_id)
        user_states.pop(user_id, None)

        if incomplete:
            logging.critical("Server 3 Provider 2 success but missing order/phone: %r", result)
            await event.edit(
                "⚠️ **Purchase needs admin review.**\n\n"
                "The provider accepted the order but returned incomplete delivery details. Please contact admin.",
                buttons=[[_pb("🔙 Main Menu", b"main_menu", style="primary")]],
            )
            return True

        await event.edit(
            "✅ **Number Reserved!**\n\n"
            f"🌍 Country: **{state.get('country')}**\n"
            f"📱 Number: `{phone}`\n"
            f"💰 Charged: **₹{retail_price}**\n\n"
            "Login to Telegram with this number, then tap **Get OTP**.",
            buttons=[
                [_pb("🔐 Get OTP", f"server3_startotp_{local_id}".encode(), style="success")],
                [_pb("🔙 Main Menu", b"main_menu", style="primary")],
            ],
        )
        try:
            buyer_name = await get_display_name(user_id)
            updated_user = await users_col.find_one({"user_id": user_id})
            new_balance = float((updated_user or {}).get("balance", 0) or 0)
            await log_event(
                "🛒 **New Account Purchase**\n"
                "🖥️ Server: **Server 3**\n"
                "🛰️ Provider: **Provider 2**\n"
                f"👤 Buyer: {buyer_name} (`{user_id}`)\n"
                f"📱 Phone: `{phone}`\n"
                f"🌍 Country: {state.get('country')} ({state.get('country_code')})\n"
                f"💰 Retail: ₹{retail_price}\n"
                f"🧾 Supplier cost: ₹{actual_pricing['wholesale_inr']}\n"
                f"👛 Balance After: ₹{new_balance}\n"
                f"🕐 Time: {now_ist().strftime('%d/%m/%Y %H:%M:%S')} IST"
            )
            await public_log_event(
                "🛒 **New Purchase**\n"
                "🖥️ Server: **Server 3**\n"
                "🛰️ Provider: **Provider 2**\n"
                f"👤 User ID: `{mask_user_id(user_id)}`\n"
                f"📱 Number: `{mask_public_phone(phone)}`\n"
                f"🌍 Country: **{state.get('country')}**\n"
                f"💰 Amount: **₹{retail_price}**\n\n"
                "💙 **Thank you for your purchase!**"
            )
        except Exception:
            pass
        return True

    for prefix, mode in (
        ("server3_startotp_", "start"),
        ("server3_restartotp_", "restart"),
        ("server3_checkotp_", "check"),
    ):
        if data.startswith(prefix):
            local_id = data[len(prefix):].strip()
            order = await _server3_get_order(local_id, user_id)
            if not order:
                await safe_callback_answer(event, "❌ Order not found.", alert=True)
                return True
            await safe_callback_answer(event, "Checking OTP...", alert=False)
            if mode == "check":
                # Check buttons belong to temporary waiting/status messages, so
                # updating that status message is fine.
                await _server3_poll_order_status(event, order, local_id, attempts=6)
            else:
                # Number Reserved and OTP Received are permanent receipts.
                # Never edit either one when Get OTP / Request New OTP is tapped.
                working = await bot.send_message(
                    event.chat_id,
                    "⏳ **Checking OTP...**",
                )
                worker = _Server3MessageEditor(
                    bot,
                    event.chat_id,
                    working.id,
                )
                await _server3_start_otp(worker, order, local_id)
            return True

    return False

async def ext_server3_message(event, user_id: int, state: dict) -> bool:
    """Typed country search for Provider 1 / Provider 2."""
    action = state.get("action")
    if action not in ("server3_p1_search_country", "server3_p2_search_country"):
        return False
    if state.get("step") != "await_query":
        return False
    _consume_prompt(event, user_id)
    query = (event.message.text or "").strip()
    if action == "server3_p1_search_country":
        items = await server3_server.provider1_stock()
        matches = _server3_provider1_matches(items, query)
        if not matches:
            await event.respond(
                fancy(f"❌ No Provider 1 country/account found for `{query}`."),
                buttons=[
                    [_pb("🔎 Search Again", "server3_p1_search_country")],
                    [_pb("📋 All", "server3_p1")],
                ],
            )
            return True
        matches = await _server3_sort_provider1_items(matches)
        user_states[user_id] = {"action": "server3_p1_search_results", "query": query, "matches": matches}
        if len(_s3_search_cache) > 3000:
            _s3_search_cache.clear()
        _s3_search_cache[(user_id, "p1")] = {"query": query, "matches": matches}
        user_nav_context.setdefault(user_id, {})["server3_p1"] = "server3_p1_search_page_0"
        msg, buttons = await build_server3_provider1_search_results(user_id, 0)
        await event.respond(msg, buttons=buttons)
        return True
    countries = await server3_server.provider2_countries()
    matches = _server3_provider2_matches(countries, query)
    if not matches:
        await event.respond(
            fancy(f"❌ No Provider 2 country found for `{query}`."),
            buttons=[
                [_pb("🔎 Search Again", "server3_p2_search_country")],
                [_pb("📋 All Countries", "server3_p2")],
            ],
        )
        return True
    user_states[user_id] = {"action": "server3_p2_search_results", "query": query, "matches": matches}
    _s3_search_cache[(user_id, "p2")] = {"query": query, "matches": matches}
    user_nav_context.setdefault(user_id, {})["server3_p2"] = "server3_p2_search_page_0"
    msg, buttons = await build_server3_provider2_search_results(user_id, 0)
    await event.respond(msg, buttons=buttons)
    return True


# ── 27.3 OTP RECEIVER EXTRAS · SESSION SAFETY ───────────────────────
_ACCESS_UNSET = {
    "access_expires_at": "", "access_expired": "", "access_expired_at": "",
    "conn_status": "", "conn_updated_at": "", "conn_last_error": "",
    "conn_retry_after": "", "conn_last_ok_at": "", "monitor_disabled": "",
}

def _acc_btn(text, data):
    return color_btn(text, data, "default")

async def send_inactive_account_admin_notice(account_doc, reason: str = "Session inactive"):
    """Admin DM for an unsold account whose session died: Replace / Remove buttons."""
    if not account_doc:
        return
    acc_id = account_doc.get("_id")
    text = (
        "⚠️ **Inactive stock detected**\n\n"
        f"• 📞 Number: `{account_doc.get('phone', 'N/A')}`\n"
        f"• 👤 Name: `{account_doc.get('tg_name') or 'Unknown'}`\n"
        f"• 🌍 Country: `{account_doc.get('country', 'N/A')}`\n"
        f"• 🗂️ Category: `{account_doc.get('category', 'N/A')}`\n"
        f"• 💰 Price: `₹{account_doc.get('price', 0)}`\n"
        f"• ❌ Reason: `{str(reason)[:160]}`\n\n"
        "Choose an action:"
    )
    buttons = [
        [_acc_btn("♻️ Replace Session", f"inactive_replace_{acc_id}")],
    ]
    for admin_id in await get_all_admin_ids():
        try:
            await bot.send_message(admin_id, fancy(text), buttons=buttons)
        except Exception as e:
            log.error(f"Could not send inactive-stock action to {admin_id}: {e}")

async def acc_invalid_notifier(doc, reason, was_sold: bool):
    """Called by AccountManager the first time a stored session turns invalid."""
    if not was_sold:
        await send_inactive_account_admin_notice(doc, reason)
        await log_event(f"⚠️ **Invalid stock session**\n• Number: `{(doc or {}).get('phone')}`\n• Marked inactive")
        return
    for admin_id in await get_all_admin_ids():
        try:
            await bot.send_message(admin_id, fancy(
                "⚠️ **Purchased account session invalid**\n\n"
                f"• 📞 Number: `{(doc or {}).get('phone')}`\n"
                f"• 👤 Buyer: `{(doc or {}).get('buyer_id')}`\n"
                "• Status stays **sold**. The buyer's Request New OTP will report an invalid session — "
                "replace or refund manually if needed."))
        except Exception:
            pass

def _sold_fields(now: Optional[datetime] = None) -> dict:
    """Fields every sale must set so the 72h OTP window works (UTC, like sold_at)."""
    now = now or datetime.utcnow()
    return {
        "sold_at": now,
        "access_expires_at": now + ACCESS_VALIDITY,
        "first_otp_sent": False,
    }

async def render_sessions(phone: str):
    auths = await acc_mgr.get_authorizations(phone)
    if auths is None:
        return fancy(f"❌ Could not fetch sessions for `{phone}`. The account's monitoring client may be offline."), None
    if not auths:
        return fancy(f"📱 No active sessions found for `{phone}`."), [[_acc_btn("Close", "close_sessions")]]
    lines = [f"📱 **Active Sessions** — `{phone}`\n"]
    buttons = []
    for a in auths:
        date_str = a.date_active.strftime("%d/%m/%Y %H:%M") if a.date_active else "N/A"
        tag = " ⭐ (bot's session — used for OTP delivery)" if a.current else ""
        lines.append(
            f"{'⭐' if a.current else '📟'} {a.device_model or 'Unknown device'}{tag}\n"
            f"   • App: {a.app_name} {a.app_version}\n"
            f"   • Platform: {a.platform} {a.system_version}\n"
            f"   • Last active: {date_str}\n"
            f"   • IP: {a.ip} ({a.country})\n"
        )
        label = (a.device_model or "device")[:20]
        if a.current:
            buttons.append([_acc_btn("⚠️ Terminate Bot's Session", f"termcurr_{phone}_{a.hash}")])
        else:
            buttons.append([_acc_btn(f"❌ Terminate: {label}", f"termsess_{phone}_{a.hash}")])
    buttons.append([_acc_btn("🔄 Refresh", f"sessions_{phone}")])
    buttons.append([_acc_btn("🏠 Home", "main_menu"), _acc_btn("Close", "close_sessions")])
    return RAW + "\n".join(lines), buttons

async def _edit_quiet(event, text, buttons=None):
    try:
        await event.edit(text, buttons=buttons)
    except MessageNotModifiedError:
        pass

async def ext_accounts_callback(event, data: str, user_id: int) -> bool:
    # ── Request New OTP (72h window, reconnect-aware)
    if data.startswith("resend_"):
        phone = data[len("resend_"):]
        res = await acc_mgr.request_again(user_id, phone)
        await safe_callback_answer(event, res["message"], alert=True)
        return True

    if data.startswith("open_sessions_"):
        phone = data[len("open_sessions_"):]
        doc = await accounts_col.find_one({"phone": phone, "status": "sold"}, sort=[("sold_at", -1)])
        if not doc or str(doc.get("buyer_id")) != str(user_id):
            await safe_callback_answer(event, "❌ Not your number.", alert=True)
            return True
        text, buttons = await render_sessions(phone)
        await bot.send_message(event.chat_id, text, buttons=buttons)
        await safe_callback_answer(event)
        return True

    if data.startswith(("sessions_", "termcurr_", "termcurrok_", "termsess_", "termsessok_")):
        parts = data.split("_", 2)
        phone = parts[1]
        doc = await accounts_col.find_one({"phone": phone, "status": "sold"}, sort=[("sold_at", -1)])
        if not doc or str(doc.get("buyer_id")) != str(user_id):
            await safe_callback_answer(event, "❌ Not your number.", alert=True)
            return True
        kind = parts[0]
        hash_str = parts[2] if len(parts) > 2 else ""
        if kind == "sessions":
            text, buttons = await render_sessions(phone)
            await _edit_quiet(event, text, buttons)
            await safe_callback_answer(event)
        elif kind == "termcurr":
            await safe_callback_answer(event, "⚠️ This is the bot's own OTP session! Terminating it stops further OTPs.", alert=True)
            await _edit_quiet(event, fancy(
                "⚠️ **Are you sure?**\n\n"
                f"This is the bot's own session for `{phone}` — the one used to forward OTPs to you.\n\n"
                "• You will not receive any further OTPs on this number.\n"
                "• You will not be able to manage sessions here anymore.\n\n"
                "This cannot be undone from this bot. Proceed?"),
                [[_acc_btn("⚠️ Yes, Terminate Anyway", f"termcurrok_{phone}_{hash_str}")],
                 [_acc_btn("❌ Cancel", f"sessions_{phone}")]])
        elif kind == "termcurrok":
            ok, msg = await acc_mgr.terminate_own_session(phone)
            if ok:
                await safe_callback_answer(event, "✅ Bot's session terminated. OTP delivery stopped.", alert=True)
                await _edit_quiet(event, fancy(
                    f"🔒 **Bot's session for** `{phone}` **has been terminated.**\n\n"
                    "You will no longer receive OTPs on this number through this bot."))
            else:
                await safe_callback_answer(event, f"❌ {msg}"[:200], alert=True)
        elif kind == "termsess":
            await _edit_quiet(event, fancy(
                "⚠️ **Terminate this session?**\n\n"
                f"This device will be logged out of `{phone}` immediately. This cannot be undone."),
                [[_acc_btn("✅ Yes, Terminate", f"termsessok_{phone}_{hash_str}")],
                 [_acc_btn("❌ Cancel", f"sessions_{phone}")]])
            await safe_callback_answer(event)
        elif kind == "termsessok":
            try:
                hash_id = int(hash_str)
            except ValueError:
                await safe_callback_answer(event, "❌ Invalid session.", alert=True)
                return True
            ok, msg = await acc_mgr.terminate_session(phone, hash_id)
            await safe_callback_answer(event, (("✅ " if ok else "❌ ") + msg)[:200], alert=True)
            text, buttons = await render_sessions(phone)
            await _edit_quiet(event, text, buttons)
        return True

    if data == "close_sessions":
        try:
            await event.delete()
        except Exception:
            pass
        await safe_callback_answer(event)
        return True

    # ── Inactive stock quick actions (admin)
    if data.startswith(("inactive_remove_", "inactive_replace_")):
        if not await is_admin(user_id):
            await safe_callback_answer(event, "❌ Access denied.", alert=True)
            return True
        replace = data.startswith("inactive_replace_")
        try:
            oid = ObjectId(data.split("_", 2)[2])
        except Exception:
            await safe_callback_answer(event, "❌ Invalid account ID.", alert=True)
            return True
        account = await accounts_col.find_one({"_id": oid})
        if not account:
            await safe_callback_answer(event, "❌ Account already removed/not found.", alert=True)
            return True
        phone = account.get("phone", "N/A")
        if not replace:
            await safe_callback_answer(event, "🔒 Stock can't be removed once it is added.", alert=True)
            return True
        if False:
            res = await accounts_col.delete_one({"_id": oid})
            if res.deleted_count:
                with contextlib.suppress(Exception):
                    await acc_mgr.remove_client(phone)
                await event.edit(fancy(f"🗑️ **Removed from stock**\n\n• 📞 Number: `{phone}`\nAccount deleted from the database."), buttons=None)
                await safe_callback_answer(event, "✅ Removed")
            else:
                await safe_callback_answer(event, "❌ Could not remove account.", alert=True)
            return True
        user_states[user_id] = {"action": "replace_inactive_session", "step": "await_session", "account_id": str(oid)}
        await event.edit(fancy(
            "♻️ **Replace inactive session**\n\n"
            f"• 📞 Number: `{phone}`\n• 👤 Name: `{account.get('tg_name', 'Unknown')}`\n"
            f"• 🌍 Country: `{account.get('country', 'N/A')}`\n• 💰 Price: `₹{account.get('price', 0)}`\n\n"
            "Send the new Telethon StringSession for this same account. It is validated before the account returns to stock."),
            buttons=[[_acc_btn("❌ Cancel", "admin")]])
        await safe_callback_answer(event)
        return True
    return False

async def ext_accounts_message(event, user_id: int, state: dict) -> bool:
    if state.get("action") != "replace_inactive_session" or state.get("step") != "await_session":
        return False
    if not await is_admin(user_id):
        user_states.pop(user_id, None)
        return True
    session_str = (event.message.text or "").strip()
    cancel = [[_acc_btn("❌ Cancel", "admin")]]
    if not session_str:
        await event.respond(fancy("❌ Empty session. Send a valid Telethon StringSession."))
        return True
    try:
        oid = ObjectId(state["account_id"])
    except Exception:
        user_states.pop(user_id, None)
        await event.respond(fancy("❌ Account reference expired. Start again."))
        return True
    account = await accounts_col.find_one({"_id": oid})
    if not account:
        user_states.pop(user_id, None)
        await event.respond(fancy("❌ Account no longer exists."))
        return True
    phone = account.get("phone")
    old_session = account.get("session_string")
    try:
        ok = await acc_mgr.add_client(phone, session_str)
    except Exception as e:
        ok = False
        log.error(f"Replacement session add failed for {phone}: {e}")
    if ok:
        ok, reason = await acc_mgr.validate_client(phone)
    else:
        reason = "session could not be opened"
    if not ok:
        with contextlib.suppress(Exception):
            await acc_mgr.remove_client(phone)
        if old_session:
            with contextlib.suppress(Exception):
                await acc_mgr.add_client(phone, old_session)
        await event.respond(fancy(f"❌ **New session is invalid.**\n\n`{str(reason)[:140]}`\n\nAccount is still inactive. Send another valid session:"), buttons=cancel)
        return True
    me = None
    with contextlib.suppress(Exception):
        me = await acc_mgr.clients[phone].get_me()
    name = format_telegram_name(me)
    await accounts_col.update_one({"_id": oid}, {
        "$set": {"session_string": session_str, "status": "available", "tg_name": name,
                 "tg_user_id": getattr(me, "id", None), "tg_username": getattr(me, "username", None),
                 "session_replaced_at": datetime.utcnow(), "session_replaced_by": user_id},
        "$unset": {"inactive_reason": "", "inactive_at": "", "buyer_id": "", "sold_at": "",
                   "first_otp_sent": "", **_ACCESS_UNSET},
    })
    user_states.pop(user_id, None)
    await event.respond(fancy(
        "✅ **Session replaced**\n\n"
        f"• 📞 Number: `{phone}`\n• 👤 Name: `{name}`\n• Status: `available`\n\nAccount is back in stock."),
        buttons=[[_acc_btn("Admin", "admin")]])
    return True


# ── 27.4 STOCK ANNOUNCEMENTS + UPLOAD METHODS ───────────────────────
def _stock_query(country_code: str, category=None, year=None, server: int = 1) -> dict:
    q: Dict[str, Any] = {"country_code": country_code, "status": "available"}
    if category:
        q["category"] = category
    if year == "none":
        q["year"] = {"$in": [None, ""]}
    elif year:
        q["year"] = str(year)
    if server == 1:
        q["$or"] = [{"server": 1}, {"server": {"$exists": False}}]
    else:
        q["server"] = server
    return q

async def _get_or_create_stock_deeplink(country_code: str, category, year) -> Optional[str]:
    """Short Mongo-backed /start token so country/category names with spaces are safe."""
    try:
        uname = (await get_bot_username()).lstrip("@").strip()
        if not uname:
            return None
        key = {"country_code": country_code, "category": category or "", "year": str(year or ""), "bot_username": uname}
        existing = await stock_deeplinks_col.find_one(key)
        if existing and existing.get("token"):
            token = str(existing["token"])
        else:
            token = secrets.token_urlsafe(9).rstrip("=")
            await stock_deeplinks_col.insert_one({**key, "token": token, "created_at": datetime.utcnow()})
        return f"https://t.me/{uname}?start=stk_{token}"
    except Exception as e:
        log.error(f"Could not create stock deep link: {e}")
        return None

async def announce_stock_update(ctx_: dict, added: int):
    """One public 'Stock Updated' post with a Buy This Stock deep-link button."""
    channel = await _announcement_channel()
    if not channel or int(added or 0) <= 0:
        return
    try:
        cc = ctx_["country_code"]
        category, year = ctx_.get("category"), ctx_.get("year")
        c = await countries_col.find_one({"code": cc}) or {}
        price = float(await get_cat_price(cc, category, c.get("price", ctx_.get("price", 0))))
        total = await accounts_col.count_documents(_stock_query(cc, category, year, int(ctx_.get("server", 1))))
        link = await _get_or_create_stock_deeplink(cc, category, year)
        flag = c.get("flag") or COUNTRY_FLAGS.get(cc, "🌍")
        text = (
            "📦 **Stock Updated!**\n\n"
            f"• 🌍 Country: {flag} {c.get('name', ctx_.get('country_name', cc))}\n"
            f"• 🗂️ Category: `{category or 'General'}`" + (f" • `{year}`" if year else "") + "\n"
            f"• ➕ New Stock Added: `{int(added)}`\n"
            f"• 📦 Available Now: `{total}`\n"
            f"• 💰 Price: `₹{price}`\n"
            f"• 🕐 `{now_ist().strftime('%d/%m/%Y %H:%M:%S')} IST`"
        )
        buttons = [[_pu("🛒 Buy This Stock", link)]] if link else None
        await bot.send_message(channel, fancy(text), buttons=buttons)
    except Exception as e:
        log.error(f"Failed to send stock announcement: {e}")

async def open_stock_deeplink(event, user_id: int, payload: str) -> bool:
    """Resolve stk_<token> and open that exact Server 1 country/category/year row."""
    if not payload.startswith("stk_"):
        return False
    token = payload[4:].strip()
    doc = await stock_deeplinks_col.find_one({"token": token}) if token else None
    back = [[color_btn("Browse Accounts", "store", "default")]]
    if not doc:
        await event.respond(fancy("❌ This stock link is invalid."), buttons=back)
        return True
    cc, category, year = doc.get("country_code"), doc.get("category") or None, doc.get("year") or None
    c = await countries_col.find_one({"code": cc, "is_active": True})
    stock = await accounts_col.count_documents(_stock_query(cc, category, year)) if c else 0
    if not c or stock <= 0:
        await event.respond(fancy("❌ This stock is currently sold out.\n\nYou can browse the latest available stock below."), buttons=back)
        return True
    user_states[user_id] = {"server": 1, "category": category, "year": year}
    rows = [[color_btn("✅ Buy 1 Account", f"buy:{cc}", "default")]]
    if stock >= 2:
        rows.append([color_btn("📦 Bulk Buy", f"bulk_setup:{cc}", "default")])
    rows.append([color_btn("◀️ Back", "store", "default")])
    await event.respond(fancy(
        "🔥 **Stock opened from announcement**\n\n"
        f"• 🌍 Country: {c.get('flag','')} {c['name']}\n"
        f"• 🗂️ Category: `{category or 'General'}`" + (f" • `{year}`" if year else "") + "\n"
        f"• 💰 Price: `₹{c['price']}`\n"
        f"• 📦 Stock: `{stock}`\n\n"
        "Tap below to continue with your purchase."), buttons=rows)
    return True

# ── upload: choose a method, then phone-login / session-string / file ──
async def _begin_upload(event, user_id: int, srv_n, cc: str, cat_name: str, year=None):
    c = await countries_col.find_one({"code": cc})
    if not c:
        await event.answer("❌ Country not found.", alert=True)
        return
    user_states[user_id] = {
        "state": "upload_menu", "country_code": cc, "country_name": c["name"],
        "price": float(await get_cat_price(cc, cat_name, c["price"])), "category": cat_name, "server": int(srv_n),
        "year": str(year) if year else None, "twofa_password": "",
    }
    yr = f" • {year}" if year else ""
    await event.edit(fancy(
        f"📦 **Upload Sessions — {c['flag']} {c['name']} ({cat_name}{yr}) • Server {srv_n}**\n\n"
        "Choose how you want to add the account(s):"),
        buttons=[
            [color_btn("📞 Phone + OTP Login", "upm:phone", "default")],
            [color_btn("🔑 Session String", "upm:string", "default")],
            [color_btn("📁 Session File / ZIP", "upm:file", "default")],
            [color_btn("❌ Cancel", "admin", "default")],
        ])

async def _upload_file_prompt(event, user_id: int):
    st = user_states.get(user_id) or {}
    default_2fa = await get_setting("default_2fa", "")
    hint = f"\n\n💡 Default 2FA: `{default_2fa}`" if default_2fa else ""
    user_states[user_id] = {**st, "state": "waiting_zip"}
    await event.edit(fancy(
        "📁 **Upload session files**\n\n"
        "Step 1 (optional): send 2FA password as text.\n"
        f"If not sent, default 2FA will be used.{hint}\n"
        "Step 2: send the **.zip** or **.session** file."),
        buttons=[[color_btn("❌ Cancel", "admin", "default")]])

def _upload_ctx(st: dict) -> dict:
    return {k: st.get(k) for k in ("country_code", "country_name", "price", "category", "server", "year")}

async def _register_uploaded_account(admin_id: int, ctx_: dict, phone: str, session_str: str,
                                     twofa: str, me=None) -> str:
    """Insert one account into stock (dedup on phone) and start its OTP listener.
    Returns 'added' | 'duplicate' | 'invalid'."""
    phone = str(phone).lstrip("+") if not str(phone).startswith("+") else str(phone)
    if await accounts_col.find_one({"phone": phone, "status": {"$in": ["available", "sold"]},
                                    "access_expired": {"$ne": True}}):
        return "duplicate"
    flag = COUNTRY_FLAGS.get(ctx_["country_code"], "🌍")
    await accounts_col.insert_one({
        "phone": phone, "session_string": session_str,
        "country": ctx_["country_name"], "country_code": ctx_["country_code"], "country_flag": flag,
        "price": ctx_["price"], "category": ctx_["category"],
        "server": ctx_.get("server", 1), "year": ctx_.get("year"),
        "twofa_password": twofa or await get_setting("default_2fa", ""),
        "status": "available", "added_at": datetime.utcnow(),
        "tg_name": format_telegram_name(me) if me else "Unknown",
        "tg_user_id": getattr(me, "id", None), "tg_username": getattr(me, "username", None),
    })
    if acc_mgr is not None:
        ok = False
        with contextlib.suppress(Exception):
            ok = await acc_mgr.add_client(phone, session_str)
        if not ok:     # dead / unusable session: never put it on sale
            await accounts_col.delete_many({"phone": phone, "status": {"$in": ["available", "inactive"]},
                                            "session_string": session_str})
            return "invalid"
    return "added"

async def _finish_single_upload(event, user_id: int, st: dict, phone, session_str, twofa, me):
    ctx_ = _upload_ctx(st)
    res = await _register_uploaded_account(user_id, ctx_, phone, session_str, twofa, me)
    user_states.pop(user_id, None)
    if res != "added":
        why = "already in stock" if res == "duplicate" else "session is invalid / unusable"
        await event.respond(fancy(f"⚠️ `{phone}` skipped — {why}."),
                            buttons=[[color_btn("Admin", "admin", "default")]])
        return
    await event.respond(fancy(
        f"✅ **Account added**\n\n• 📞 `{phone}`\n• 🌍 {ctx_['country_name']} • {ctx_['category']}\n"
        f"• 💰 ₹{ctx_['price']}"), buttons=[[color_btn("Admin", "admin", "default")]])
    await log_event(
        "📦 **Stock Added**\n"
        f"• Admin: {await get_display_name(user_id)} (`{user_id}`)\n"
        f"• Phone: `{phone}`\n• Country: {ctx_['country_name']}\n• Category: {ctx_['category']}\n"
        f"• Price: ₹{ctx_['price']}\n• Added: 1\n• Time: {now_ist().strftime('%d/%m/%Y %H:%M:%S')} IST")
    await announce_stock_update(ctx_, 1)

async def ext_upload_callback(event, data: str, user_id: int) -> bool:
    if not data.startswith("upm:"):
        return False
    if not await is_admin(user_id):
        await event.answer("❌ Access denied.", alert=True)
        return True
    st = user_states.get(user_id)
    if not st or "country_code" not in st:
        await event.answer("❌ Session expired. Start again.", alert=True)
        return True
    method = data.split(":", 1)[1]
    cancel = [[color_btn("❌ Cancel", "admin", "default")]]
    if method == "file":
        await _upload_file_prompt(event, user_id)
    elif method == "phone":
        user_states[user_id] = {**st, "action": "up_phone", "step": "phone"}
        await event.edit(fancy("📞 **Phone + OTP login**\n\nSend the phone number with country code, e.g. `+919876543210`."), buttons=cancel)
    elif method == "string":
        user_states[user_id] = {**st, "action": "up_string", "step": "session"}
        await event.edit(fancy("🔑 **Session string**\n\nSend the Telethon StringSession."), buttons=cancel)
    return True

async def ext_upload_message(event, user_id: int, st: dict) -> bool:
    action = st.get("action")
    if action not in ("up_phone", "up_string"):
        return False
    if not await is_admin(user_id):
        user_states.pop(user_id, None)
        return True
    text = (event.message.text or "").strip()
    cancel = [[color_btn("❌ Cancel", "admin", "default")]]

    async def _fail(msg: str):
        tc = st.get("temp_client")
        if tc:
            with contextlib.suppress(Exception):
                await tc.disconnect()
        user_states.pop(user_id, None)
        await event.respond(fancy(msg), buttons=[[color_btn("Admin", "admin", "default")]])

    if action == "up_phone":
        step = st["step"]
        if step == "phone":
            tc = TelegramClient(StringSession(), API_ID, API_HASH)
            await tc.connect()
            try:
                sent = await tc.send_code_request(text)
            except Exception as e:
                with contextlib.suppress(Exception):
                    await tc.disconnect()
                user_states.pop(user_id, None)
                await event.respond(fancy(f"❌ Error: {e}"), buttons=cancel)
                return True
            st.update(phone=text, temp_client=tc, phone_code_hash=sent.phone_code_hash, step="otp")
            await event.respond(fancy("✉️ **OTP sent.** Send the code you received:"), buttons=cancel)
            return True
        tc = st.get("temp_client")
        if step == "otp":
            try:
                await tc.sign_in(st["phone"], text, phone_code_hash=st.get("phone_code_hash"))
            except SessionPasswordNeededError:
                st["step"] = "2fa"
                await event.respond(fancy("🔒 **2FA password required.** Send the password:"), buttons=cancel)
                return True
            except Exception as e:
                await _fail(f"❌ Login failed: {e}")
                return True
        elif step == "2fa":
            try:
                await tc.sign_in(password=text)
                st["twofa_password"] = text
            except Exception as e:
                await _fail(f"❌ 2FA failed: {e}")
                return True
        else:
            return True
        me = await tc.get_me()
        session_str = tc.session.save()
        with contextlib.suppress(Exception):
            await tc.disconnect()
        await _finish_single_upload(event, user_id, st, st["phone"], session_str, st.get("twofa_password", ""), me)
        return True

    # action == "up_string"
    step = st["step"]
    if step == "session":
        tc = TelegramClient(StringSession(text), API_ID, API_HASH)
        try:
            await tc.connect()
            if not await tc.is_user_authorized():
                await _fail("❌ Invalid session.")
                return True
            me = await tc.get_me()
            st.update(phone=("+" + me.phone) if me.phone and not str(me.phone).startswith("+") else me.phone,
                      session_str=tc.session.save(), me=me, step="ask_2fa")
            await tc.disconnect()
        except Exception as e:
            with contextlib.suppress(Exception):
                await tc.disconnect()
            await _fail(f"❌ Error: {e}")
            return True
        await event.respond(fancy(f"📱 Number: `{st['phone']}`\n\n🔐 2FA password? Send it, or send `skip`."), buttons=cancel)
        return True
    if step == "ask_2fa":
        twofa = "" if text.lower() == "skip" else text
        await _finish_single_upload(event, user_id, st, st["phone"], st["session_str"], twofa, st.get("me"))
    return True


# ── 27.5 BULK BUY (Server 1: Direct OTP one-by-one / Session ZIP + 2FA) ──
def _bulk_mode_label(mode: str) -> str:
    return "Direct OTP (one by one)" if mode == "direct_otp" else "Session ZIP + 2FA"

async def _server1_release_bulk_accounts(accounts: list[dict], bulk_id=None):
    """Release only accounts reserved by this unfinished bulk purchase."""
    for acc in accounts or []:
        filt = {"_id": acc["_id"]}
        if bulk_id is not None:
            filt["bulk_order_id"] = str(bulk_id)
        await accounts_col.update_one(
            filt,
            {
                "$set": {"status": "available"},
                "$unset": {
                    "buyer_id": "",
                    "sold_at": "",
                    "bulk_order_id": "",
                    "bulk_mode": "",
                    "bulk_index": "",
                    "bulk_total": "",
                    "bulk_active": "",
                    "first_otp_sent": "",
                    **_ACCESS_UNSET,
                },
            },
        )

async def _server1_reserve_bulk_accounts(
    *,
    query: dict,
    quantity: int,
    buyer_id: int,
    bulk_id,
    mode: str,
):
    """FIFO-reserve and live-validate Server 1 stock for a bulk order."""
    cursor = accounts_col.find(query).sort("_id", 1)
    candidates = await cursor.to_list(length=None)
    selected = []

    for acc in candidates:
        claimed = await accounts_col.find_one_and_update(
            {"_id": acc["_id"], "status": "available"},
            {
                "$set": {
                    "status": "bulk_reserving",
                    "buyer_id": int(buyer_id),
                    "bulk_order_id": str(bulk_id),
                    "bulk_mode": mode,
                }
            },
        )
        if claimed is None:
            continue

        phone = acc.get("phone")
        valid, health_error = await acc_mgr.validate_client(phone)
        if not valid:
            reason = str(health_error or "session_unavailable")[:180]
            await accounts_col.update_one(
                {"_id": acc["_id"]},
                {
                    "$set": {
                        "status": "inactive",
                        "inactive_reason": reason,
                        "inactive_at": datetime.utcnow(),
                    },
                    "$unset": {
                        "buyer_id": "",
                        "bulk_order_id": "",
                        "bulk_mode": "",
                    },
                },
            )
            inactive_doc = dict(acc)
            inactive_doc["status"] = "inactive"
            await send_inactive_account_admin_notice(inactive_doc, reason)
            continue

        selected.append(acc)
        if len(selected) >= quantity:
            break

    if len(selected) < quantity:
        await _server1_release_bulk_accounts(selected, bulk_id)
        return []

    return selected

async def _server1_detach_zip_sessions_from_main(accounts: list[dict], *, bulk_id):
    """
    After a Session-ZIP has been successfully delivered, disconnect the main
    bot's live Telethon client and remove the reusable session credential from
    the main database.

    IMPORTANT: this does NOT call Telegram logout/revoke. The delivered .session
    file therefore stays valid for the buyer; only the main bot loses its copy.
    """
    removed = 0
    failures = []

    for acc in accounts:
        phone = str(acc.get("phone") or "")
        acc_id = acc.get("_id")

        # Disconnect only. Never log_out() here, because that would revoke the
        # same Telegram authorization exported into the buyer's ZIP.
        try:
            await acc_mgr.remove_client(phone)
        except Exception as exc:
            logging.warning(
                "Could not disconnect transferred Server 1 client phone=%s bulk=%s: %s",
                phone,
                bulk_id,
                exc,
            )

        try:
            result = await accounts_col.update_one(
                {
                    "_id": acc_id,
                    "bulk_order_id": str(bulk_id),
                    "bulk_mode": "session_zip",
                },
                {
                    "$unset": {"session_string": ""},
                    "$set": {
                        "session_transferred": True,
                        "session_transferred_at": datetime.utcnow(),
                        "session_removed_from_main": True,
                        "bulk_active": False,
                    },
                },
            )
            # matched_count means the intended sold record was found. A zero
            # modified_count can simply mean it had already been detached.
            if getattr(result, "matched_count", 0) > 0:
                removed += 1
            else:
                failures.append(phone or str(acc_id))
        except Exception as exc:
            failures.append(phone or str(acc_id))
            logging.error(
                "Could not remove transferred Server 1 session from DB phone=%s bulk=%s: %s",
                phone,
                bulk_id,
                exc,
            )

    return removed, failures

async def _server1_finalize_bulk_accounts(
    accounts: list[dict], *, buyer_id: int, bulk_id, mode: str
):
    total = len(accounts)
    sold_at = datetime.utcnow()
    for idx, acc in enumerate(accounts):
        await accounts_col.update_one(
            {"_id": acc["_id"], "status": "bulk_reserving", "bulk_order_id": str(bulk_id)},
            {
                "$set": {
                    "status": "sold",
                    "buyer_id": int(buyer_id),
                    "sold_at": sold_at,
                    "access_expires_at": sold_at + ACCESS_VALIDITY,
                    "access_expired": False,
                    "first_otp_sent": False,
                    "bulk_order_id": str(bulk_id),
                    "bulk_mode": mode,
                    "bulk_index": idx + 1,
                    "bulk_total": total,
                    "bulk_active": bool(mode == "direct_otp" and idx == 0),
                },
                "$unset": {"access_expired_at": ""},
            },
        )

async def _server1_create_bulk_orders(
    accounts: list[dict], *, buyer_id: int, ctx_: dict, unit_price: float, bulk_id, mode: str
):
    entries = []
    for idx, acc in enumerate(accounts):
        order_result = await orders_col.insert_one({
            "user_id": int(buyer_id),
            "phone": acc.get("phone"),
            "country": ctx_["country_name"],
            "country_code": ctx_["country_code"],
            "country_flag": ctx_.get("country_flag", ""),
            "category": ctx_.get("category"),
            "amount": unit_price,
            "twofa": acc.get("twofa_password", ""),
            "status": "bulk_waiting_otp" if mode == "direct_otp" else "bulk_session_delivered",
            "bulk_order_id": str(bulk_id),
            "bulk_mode": mode,
            "bulk_index": idx + 1,
            "bulk_total": len(accounts),
            "created_at": datetime.utcnow(),
        })
        entries.append({
            "account_id": str(acc["_id"]),
            "order_id": str(order_result.inserted_id),
            "phone": acc.get("phone"),
            "twofa_password": acc.get("twofa_password"),
            "index": idx + 1,
        })
    return entries

def _export_string_session_sqlite(session_string: str, output_base: str) -> str:
    """Convert a Telethon StringSession into a normal SQLite .session file."""
    source = StringSession(session_string)
    destination = SQLiteSession(output_base)
    destination.set_dc(source.dc_id, source.server_address, source.port)
    destination.auth_key = source.auth_key
    destination.save()
    try:
        destination.close()
    except Exception:
        pass
    return output_base if output_base.endswith(".session") else output_base + ".session"

def _build_bulk_session_zip(accounts: list[dict], country: str, bulk_id) -> str:
    temp_dir = tempfile.mkdtemp(prefix="otp_bulk_sessions_")
    zip_path = os.path.join(temp_dir, f"bulk_{str(bulk_id)[-8:]}.zip")
    manifest_lines = [
        "Bulk Session Delivery",
        f"Country: {country}",
        f"Accounts: {len(accounts)}",
        "",
        "PHONE | 2FA",
    ]

    session_paths = []
    for acc in accounts:
        phone = re.sub(r"[^0-9+]", "", str(acc.get("phone") or "unknown"))
        safe_phone = re.sub(r"[^0-9]", "", phone) or "account"
        base = os.path.join(temp_dir, safe_phone)
        session_path = _export_string_session_sqlite(str(acc.get("session_string") or ""), base)
        session_paths.append((session_path, f"{safe_phone}.session"))
        twofa = str(acc.get("twofa_password") or "Not set")
        manifest_lines.append(f"{phone} | {twofa}")

    manifest_path = os.path.join(temp_dir, "accounts.txt")
    with open(manifest_path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(manifest_lines) + "\n")

    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for session_path, arcname in session_paths:
            zf.write(session_path, arcname)
        zf.write(manifest_path, "accounts.txt")

    return zip_path

async def _send_bulk_direct_number(bulk_doc: dict, index: int, *, edit_event=None):
    accounts = list(bulk_doc.get("accounts") or [])
    if index < 0 or index >= len(accounts):
        return False
    item = accounts[index]
    phone = str(item.get("phone") or "")
    twofa = item.get("twofa_password")

    # Make sure this sold account has a live OTP listener, including after restart.
    account_doc = await accounts_col.find_one({"_id": ObjectId(item["account_id"])})
    if account_doc and phone not in acc_mgr.clients:
        session_string = account_doc.get("session_string")
        if session_string:
            await acc_mgr.add_client(phone, session_string)

    await accounts_col.update_one(
        {"_id": ObjectId(item["account_id"])},
        {"$set": {"bulk_active": True}},
    )

    total = len(accounts)
    msg = (
        f"📦 **Bulk OTP — Number {index + 1}/{total}**\n\n"
        f"📱 Number: `{phone}`\n"
    )
    if twofa:
        msg += f"🔒 2FA Password: `{twofa}`\n"
    msg += (
        "\nLogin to Telegram with this number.\n"
        "As soon as its OTP is received, the next number will be sent automatically."
    )
    buttons = [[_pb("🔄 Request New OTP", f"resend_{phone}", style="primary")]]
    if edit_event is not None:
        await edit_event.edit(msg, buttons=buttons)
    else:
        await bot.send_message(
            int(bulk_doc["user_id"]), msg, buttons=buttons
        )
    return True

async def advance_server1_bulk_after_otp(*, buyer_id: int, phone: str):
    """For Direct OTP bulk orders, OTP N unlocks and sends number N+1."""
    bulk_doc = await bulk_orders_col.find_one({
        "user_id": int(buyer_id),
        "mode": "direct_otp",
        "status": "active",
        "accounts.phone": str(phone),
    })
    if not bulk_doc:
        return

    accounts = list(bulk_doc.get("accounts") or [])
    current_index = int(bulk_doc.get("current_index", 0) or 0)
    if current_index >= len(accounts):
        return
    current = accounts[current_index]
    if str(current.get("phone")) != str(phone):
        return

    await accounts_col.update_one(
        {"_id": ObjectId(current["account_id"])},
        {"$set": {"bulk_active": False, "bulk_otp_completed": True}},
    )
    await orders_col.update_one(
        {"_id": ObjectId(current["order_id"])},
        {"$set": {"status": "otp_received", "otp_received_at": datetime.utcnow()}},
    )

    next_index = current_index + 1
    if next_index >= len(accounts):
        await bulk_orders_col.update_one(
            {"_id": bulk_doc["_id"]},
            {"$set": {"status": "completed", "current_index": next_index, "completed_at": datetime.utcnow()}},
        )
        await bot.send_message(
            int(buyer_id),
            f"✅ **Bulk OTP Completed**\n\nAll **{len(accounts)}** numbers have completed OTP delivery.",
            buttons=[[_pb("🔙 Main Menu", b"main_menu", style="primary")]],
        )
        return

    await bulk_orders_col.update_one(
        {"_id": bulk_doc["_id"]},
        {"$set": {"current_index": next_index, "updated_at": datetime.utcnow()}},
    )
    bulk_doc["current_index"] = next_index
    await _send_bulk_direct_number(bulk_doc, next_index)

async def execute_server1_bulk_purchase(event, user_id: int, state: dict):
    cc = str(state.get("country_code") or "")
    country_name = str(state.get("country_name") or cc)
    category, year = state.get("category"), state.get("year")
    retail = float(state.get("price", 0) or 0)
    quantity = int(state.get("quantity", 0) or 0)
    mode = str(state.get("mode") or "")
    ctx_ = {"country_code": cc, "country_name": country_name, "category": category,
            "country_flag": state.get("country_flag", "")}
    query = _stock_query(cc, category, year)
    back_btn = [[_pb("🔙 Back to Server 1", "store")]]

    if mode not in {"direct_otp", "session_zip"} or quantity < 2:
        await safe_callback_answer(event, "Bulk setup expired. Please start again.", alert=True)
        return False

    total_retail = round(retail * quantity, 2)
    stock = await accounts_col.count_documents(query)
    if stock < quantity:
        await safe_callback_answer(event, f"Only {stock} accounts are available now. Please choose a smaller quantity.", alert=True)
        return False

    user = await users_col.find_one({"user_id": int(user_id)}) or {}
    if float(user.get("balance", 0) or 0) < total_retail:
        await show_insufficient_balance(event, required=total_retail, back_data=b"store", back_label="Back to Server 1")
        return False

    bulk_id = ObjectId()
    await safe_callback_answer(event, "Preparing bulk order...", alert=False)
    await event.edit(fancy(
        "⏳ **Preparing Bulk Order**\n\n"
        f"🌍 Country: **{country_name}**\n"
        f"📦 Quantity: **{quantity}**\n"
        f"🚚 Mode: **{_bulk_mode_label(mode)}**\n\n"
        "Checking account sessions and reserving stock..."))

    selected = await _server1_reserve_bulk_accounts(
        query=query, quantity=quantity, buyer_id=user_id, bulk_id=bulk_id, mode=mode)
    if len(selected) != quantity:
        user_states.pop(user_id, None)
        await event.edit(fancy(
            "❌ **Not enough active accounts are available right now.**\n\n"
            "Some listed stock failed the live session check. No amount was charged."), buttons=back_btn)
        return False

    zip_path = None
    if mode == "session_zip":
        try:
            zip_path = _build_bulk_session_zip(selected, country_name, bulk_id)
        except Exception as e:
            logging.exception("Could not build Server 1 bulk session ZIP: %s", e)
            await _server1_release_bulk_accounts(selected, bulk_id)
            user_states.pop(user_id, None)
            await event.edit(fancy("❌ Could not prepare the session package. No amount was charged."), buttons=back_btn)
            return False
    old_withdrawable = float(user.get("withdrawable", 0) or 0)
    withdrawable_deducted = min(old_withdrawable, total_retail)
    deduction = await users_col.update_one(
        {"user_id": int(user_id), "balance": {"$gte": total_retail}},
        {
            "$inc": {"balance": -total_retail},
            "$set": {"withdrawable": max(0.0, old_withdrawable - total_retail)},
        },
    )
    if deduction.modified_count == 0:
        await _server1_release_bulk_accounts(selected, bulk_id)
        if zip_path:
            shutil.rmtree(os.path.dirname(zip_path), ignore_errors=True)
        user_states.pop(user_id, None)
        await event.edit(
            "❌ Your balance changed before checkout. No purchase was completed.",
            buttons=[[_pb("🔙 Server 1", b"store", style="primary")]],
        )
        return False

    entries = []
    try:
        await _server1_finalize_bulk_accounts(
            selected,
            buyer_id=user_id,
            bulk_id=bulk_id,
            mode=mode,
        )
        entries = await _server1_create_bulk_orders(
            selected, buyer_id=user_id, ctx_=ctx_, unit_price=retail, bulk_id=bulk_id, mode=mode,
        )
        await bulk_orders_col.insert_one({
            "_id": bulk_id,
            "user_id": int(user_id),
            "country": country_name,
            "country_code": cc,
            "category": category,
            "year": year,
            "price": retail,
            "quantity": quantity,
            "total_amount": total_retail,
            "mode": mode,
            "status": "active" if mode == "direct_otp" else "delivering",
            "current_index": 0,
            "accounts": entries,
            "withdrawable_deducted": withdrawable_deducted,
            "created_at": datetime.utcnow(),
        })
    except Exception as e:
        logging.exception("Server 1 bulk checkout failed after balance deduction: %s", e)
        await users_col.update_one(
            {"user_id": int(user_id)},
            {"$inc": {"balance": total_retail, "withdrawable": withdrawable_deducted}},
        )
        await _server1_release_bulk_accounts(selected, bulk_id)
        if zip_path:
            shutil.rmtree(os.path.dirname(zip_path), ignore_errors=True)
        user_states.pop(user_id, None)
        await event.edit(
            "❌ Bulk checkout failed. Your full amount was restored.",
            buttons=[[_pb("🔙 Server 1", b"store", style="primary")]],
        )
        return False

    user_states.pop(user_id, None)

    if mode == "direct_otp":
        bulk_doc = await bulk_orders_col.find_one({"_id": bulk_id})
        await _send_bulk_direct_number(bulk_doc, 0, edit_event=event)
        await log_event(
            f"📦 **Server 1 Bulk Purchase**\n"
            f"👤 Buyer: `{user_id}`\n"
            f"🌍 Country: {country_name}\n"
            f"🔐 Mode: Direct OTP\n"
            f"📦 Quantity: {quantity}\n"
            f"💰 Total: ₹{total_retail}"
        )
        await public_log_event(
            f"📦 **New Bulk Purchase**\n"
            f"🖥️ Server: **Server 1**\n"
            f"👤 User ID: `{mask_user_id(user_id)}`\n"
            f"🌍 Country: **{country_name}**\n"
            f"📦 Quantity: **{quantity}**\n"
            f"🚚 Mode: **Direct OTP**\n"
            f"💰 Amount: **₹{total_retail}**\n"
            f"🕐 {datetime.utcnow().strftime('%d/%m/%Y %H:%M:%S')} IST\n\n"
            "💙 **Thank you for your purchase!**"
        )
        return True

    # Session ZIP mode: deliver all session files + 2FA manifest in one package.
    try:
        reader_username = await get_session_reader_bot_username()
        reader_line = (
            f"\n\n🤖 Read OTP / Manage Sessions: **@{reader_username}**"
            if reader_username else
            ""
        )
        await bot.send_file(
            int(user_id),
            zip_path,
            caption=(
                f"📦 **Bulk Session Package**\n\n"
                f"🌍 Country: **{country_name}**\n"
                f"📦 Accounts: **{quantity}**\n"
                f"💰 Total: **₹{total_retail}**\n\n"
                "The ZIP contains one `.session` file per number plus `accounts.txt` with each number and its 2FA password."
                f"{reader_line}"
            ),
        )
        # Package reached the buyer. Now detach the main bot from every
        # transferred account: disconnect its listener and delete session_string
        # from the main DB WITHOUT revoking the Telegram authorization.
        removed_sessions, cleanup_failures = await _server1_detach_zip_sessions_from_main(
            selected,
            bulk_id=bulk_id,
        )

        await bulk_orders_col.update_one(
            {"_id": bulk_id},
            {
                "$set": {
                    "status": "completed",
                    "completed_at": datetime.utcnow(),
                    "main_sessions_removed": removed_sessions,
                    "main_session_cleanup_failures": cleanup_failures,
                }
            },
        )

        cleanup_note = ""
        if cleanup_failures:
            # Delivery is already successful, so never refund/release the sold
            # accounts here. Keep an audit trail and alert admins for cleanup.
            logging.critical(
                "Bulk ZIP delivered but %s main session credential(s) could not be removed; "
                "bulk=%s failures=%r",
                len(cleanup_failures),
                bulk_id,
                cleanup_failures,
            )
            cleanup_note = "\n⚠️ Session handoff completed; internal cleanup is pending for some accounts."

        success_reader_line = (
            f"\n🤖 Reader Bot: **@{reader_username}**"
            if reader_username else
            ""
        )
        success_buttons = []
        if reader_username:
            success_buttons.append([_pu("🤖 Open Reader Bot", f"https://t.me/{reader_username}")])
        success_buttons.append([_pb("🔙 Main Menu", b"main_menu", style="primary")])
        await event.edit(
            "✅ **Bulk Session ZIP Delivered**\n\n"
            f"📦 {quantity} accounts\n"
            f"💰 Charged: ₹{total_retail}\n"
            f"🔐 Main bot session copies removed: **{removed_sessions}/{quantity}**"
            f"{success_reader_line}"
            f"{cleanup_note}",
            buttons=success_buttons,
        )
        await log_event(
            f"📦 **Server 1 Bulk Purchase**\n"
            f"👤 Buyer: `{user_id}`\n"
            f"🌍 Country: {country_name}\n"
            f"🗂️ Mode: Session ZIP\n"
            f"📦 Quantity: {quantity}\n"
            f"💰 Total: ₹{total_retail}"
        )
        await public_log_event(
            f"📦 **New Bulk Purchase**\n"
            f"🖥️ Server: **Server 1**\n"
            f"👤 User ID: `{mask_user_id(user_id)}`\n"
            f"🌍 Country: **{country_name}**\n"
            f"📦 Quantity: **{quantity}**\n"
            f"🚚 Mode: **Session ZIP**\n"
            f"💰 Amount: **₹{total_retail}**\n"
            f"🕐 {datetime.utcnow().strftime('%d/%m/%Y %H:%M:%S')} IST\n\n"
            "💙 **Thank you for your purchase!**"
        )
        return True
    except Exception as e:
        logging.exception("Bulk session ZIP delivery failed: %s", e)
        # No package reached the customer: reverse the completed checkout.
        await users_col.update_one(
            {"user_id": int(user_id)},
            {"$inc": {"balance": total_retail, "withdrawable": withdrawable_deducted}},
        )
        await _server1_release_bulk_accounts(selected, bulk_id)
        for entry in entries:
            try:
                await orders_col.update_one(
                    {"_id": ObjectId(entry["order_id"])},
                    {"$set": {"status": "refunded", "refund_reason": "zip_delivery_failed"}},
                )
            except Exception:
                pass
        await bulk_orders_col.update_one(
            {"_id": bulk_id},
            {"$set": {"status": "refunded", "refund_reason": "zip_delivery_failed", "completed_at": datetime.utcnow()}},
        )
        await event.edit(
            "❌ Session package delivery failed. Your full amount was restored.",
            buttons=[[_pb("🔙 Server 1", b"store", style="primary")]],
        )
        return False
    finally:
        if zip_path:
            shutil.rmtree(os.path.dirname(zip_path), ignore_errors=True)

async def get_session_reader_bot_username() -> str:
    name = SESSION_READER_BOT_USERNAME or str(await get_setting("session_reader_bot", "") or "")
    return name.strip().lstrip("@")

def _bulk_menu(state: dict):
    price = state["price"]
    text = fancy(
        "📦 **Bulk Buy — Server 1**\n\n"
        f"🌍 Country: **{state['country_name']}**\n"
        f"🗂️ Category: `{state.get('category') or 'General'}`" + (f" • `{state['year']}`" if state.get("year") else "") + "\n"
        f"💰 Price per account: **₹{price}**\n\n"
        "Choose delivery type:")
    buttons = [
        [_pb("🔐 Direct OTP — One by One", "bulk_mode_direct")],
        [_pb("🗂️ Session ZIP + 2FA", "bulk_mode_zip")],
        [_pb("🔙 Back", f"detail:{state['country_code']}")],
    ]
    return text, buttons

async def _bulk_qty_screen(event, state: dict):
    stock = await accounts_col.count_documents(_stock_query(state["country_code"], state.get("category"), state.get("year")))
    await event.edit(fancy(
        f"📦 **{_bulk_mode_label(state['mode'])}**\n\n"
        f"🌍 Country: **{state['country_name']}**\n"
        f"💰 Per account: **₹{state['price']}**\n"
        f"📦 Available now: **{stock}**\n\n"
        f"Send quantity from **2 to {min(BULK_BUY_MAX_QTY, stock)}**."),
        buttons=[[_pb("🔙 Back", "bulk_back_setup")]])

async def ext_bulk_callback(event, data: str, user_id: int) -> bool:
    if data.startswith("bulk_setup:"):
        cc = data.split(":", 1)[1]
        st = user_states.get(user_id) or {}
        country = await countries_col.find_one({"code": cc, "is_active": True})
        if not country or st.get("server", 1) != 1:
            await safe_callback_answer(event, "Session expired. Please choose stock again.", alert=True)
            return True
        stock = await accounts_col.count_documents(_stock_query(cc, st.get("category"), st.get("year")))
        if stock < 2:
            await safe_callback_answer(event, "Bulk buy needs at least 2 accounts in stock.", alert=True)
            return True
        state = {"action": "awaiting_confirmation", "server": 1, "category": st.get("category"),
                 "year": st.get("year"), "country_code": cc, "country_name": country["name"],
                 "country_flag": country.get("flag", ""),
                 "price": float(await get_cat_price(cc, st.get("category"), country["price"]))}
        user_states[user_id] = state
        text, buttons = _bulk_menu(state)
        await event.edit(text, buttons=buttons)
        await safe_callback_answer(event)
        return True
    if data in ("bulk_back_setup", "bulk_back_quantity", "bulk_mode_direct", "bulk_mode_zip", "bulk_confirm_server1"):
        state = user_states.get(user_id)
        if not state or state.get("action") not in ("awaiting_confirmation", "bulk_buy_server1"):
            await safe_callback_answer(event, "Session expired. Please choose stock again.", alert=True)
            return True
        if data == "bulk_back_setup":
            state.update(action="awaiting_confirmation")
            for k in ("step", "mode", "quantity"):
                state.pop(k, None)
            text, buttons = _bulk_menu(state)
            await event.edit(text, buttons=buttons)
        elif data == "bulk_back_quantity":
            state["step"] = "await_quantity"
            state.pop("quantity", None)
            await _bulk_qty_screen(event, state)
        elif data in ("bulk_mode_direct", "bulk_mode_zip"):
            state.update(action="bulk_buy_server1", step="await_quantity",
                         mode="direct_otp" if data == "bulk_mode_direct" else "session_zip")
            await _bulk_qty_screen(event, state)
        else:
            if state.get("action") != "bulk_buy_server1" or state.get("step") != "confirm":
                await safe_callback_answer(event, "Bulk session expired. Please start again.", alert=True)
                return True
            await execute_server1_bulk_purchase(event, user_id, state)
            return True
        await safe_callback_answer(event)
        return True
    return False

async def ext_bulk_message(event, user_id: int, state: dict) -> bool:
    if state.get("action") != "bulk_buy_server1" or state.get("step") != "await_quantity":
        return False
    text = (event.message.text or "").strip()
    stock = await accounts_col.count_documents(_stock_query(state["country_code"], state.get("category"), state.get("year")))
    max_qty = min(BULK_BUY_MAX_QTY, stock)
    if not text.isdigit() or not (2 <= int(text) <= max_qty):
        await event.respond(fancy(f"❌ Send a valid quantity from **2 to {max_qty}**."),
                            buttons=[[_pb("🔙 Back", "bulk_back_setup")]])
        return True
    qty = int(text)
    total = round(state["price"] * qty, 2)
    state.update(quantity=qty, step="confirm")
    user = await users_col.find_one({"user_id": user_id}) or {}
    await event.respond(fancy(
        "📦 **Confirm Bulk Order**\n\n"
        f"🌍 Country: **{state['country_name']}**\n"
        f"🚚 Mode: **{_bulk_mode_label(state['mode'])}**\n"
        f"📦 Quantity: **{qty}**\n"
        f"💰 Total: **₹{total}**\n"
        f"💎 Your balance: **₹{float(user.get('balance', 0))}**"),
        buttons=[[_pb("✅ Confirm Bulk Purchase", "bulk_confirm_server1")],
                 [_pb("🔙 Back", "bulk_back_quantity")]])
    return True

# ── 27.6 REFERRAL (join reward after required joins + first-deposit %) ──
withdrawals_col = db["withdrawals"]

async def _ref_setting(key: str, default):
    doc = await settings_col.find_one({"key": key})
    return doc.get("value", default) if doc else default

async def _ref_set(key: str, value):
    await settings_col.update_one({"key": key}, {"$set": {"value": value, "updated_at": datetime.utcnow()}}, upsert=True)

async def get_referral_signup_bonus() -> float:
    return round(float(await _ref_setting("referral_signup_bonus", REFERRAL_SIGNUP_BONUS)), 2)

async def get_referral_bonus_percent() -> float:
    return float(await _ref_setting("referral_bonus_percent", REFERRAL_BONUS_PERCENT))

async def get_referral_bonus_max() -> float:
    return float(await _ref_setting("referral_bonus_max", REFERRAL_BONUS_MAX))

async def is_referral_enabled() -> bool:
    return bool(await _ref_setting("referral_enabled", True))

async def get_min_withdrawal() -> float:
    return float(await _ref_setting("min_withdrawal", 50))

def parse_start_referrer(payload: str) -> Optional[int]:
    """'ref123456' / 'ref_123456' (user id). Old 'ref_<CODE>' links are resolved by the caller."""
    if not payload.startswith("ref"):
        return None
    raw = payload[3:].lstrip("_")
    return int(raw) if raw.isdigit() else None

async def resolve_referrer(payload: str) -> Optional[int]:
    rid = parse_start_referrer(payload)
    if rid:
        return rid
    if payload.startswith("ref"):
        code = payload[3:].lstrip("_")
        ref_user = await users_col.find_one({"referral_code": code})
        return ref_user["user_id"] if ref_user else None
    return None

async def award_referral_signup_bonus(referred_user_id: int):
    """Join reward — only after ALL required joins are verified, exactly once.
    Claim row + wallet credit use deterministic receipts so a retry never pays twice."""
    referred = await users_col.find_one({"user_id": referred_user_id})
    if not referred or not referred.get("referral_signup_eligible"):
        return
    referrer_id = referred.get("referred_by")
    if not referrer_id or referrer_id == referred_user_id or not await is_referral_enabled():
        return
    referrer = await users_col.find_one({"user_id": referrer_id})
    if not referrer:
        return
    if not await is_user_member(referred_user_id):      # fail closed
        return
    required_chat_count = len(await get_force_join_chats())
    claim_id = str(referred_user_id)
    amount_cfg = await get_referral_signup_bonus()
    try:
        await referral_signup_claims_col.insert_one({
            "_id": claim_id, "referred_user_id": referred_user_id, "referrer_id": referrer_id,
            "amount": amount_cfg, "required_chats_verified": required_chat_count,
            "verified_at": datetime.utcnow(), "status": "processing", "schema_version": 2,
            "created_at": datetime.utcnow(),
        })
    except DuplicateKeyError:
        pass
    ledger = await referral_signup_claims_col.find_one({"_id": claim_id})
    if not ledger or ledger.get("status") == "paid" or ledger.get("schema_version") != 2:
        return
    if ledger.get("referrer_id") != referrer_id:
        log.error(f"Referral ledger referrer mismatch for {claim_id}")
        return
    reward = round(float(ledger["amount"]), 2)
    if not 0 <= reward <= 1000:
        log.error(f"Referral claim {claim_id} has invalid amount {reward!r}")
        return
    try:
        credit = await users_col.update_one(
            {"user_id": referrer_id, "referral_signup_credit_receipts": {"$ne": claim_id}},
            {"$inc": {"balance": reward, "withdrawable": reward, "referral_earnings": reward},
             "$addToSet": {"referral_signup_credit_receipts": claim_id}})
        if credit.modified_count != 1:
            cur = await users_col.find_one({"user_id": referrer_id})
            if not cur or claim_id not in cur.get("referral_signup_credit_receipts", []):
                raise RuntimeError(f"Signup referrer {referrer_id} disappeared before credit")
        await users_col.update_one({"user_id": referred_user_id}, {"$set": {
            "referral_signup_bonus_claimed": True, "referral_signup_bonus_status": "paid",
            "referral_signup_bonus_amount": reward, "referral_signup_bonus_referrer_id": referrer_id,
            "referral_signup_bonus_paid_at": datetime.utcnow()}})
        done = await referral_signup_claims_col.update_one(
            {"_id": claim_id, "status": {"$ne": "paid"}},
            {"$set": {"status": "paid", "paid_at": datetime.utcnow()}})
        if not done.modified_count:
            return
    except Exception as exc:
        log.exception(f"Signup referral credit failed for {referred_user_id}/{referrer_id}")
        await referral_signup_claims_col.update_one(
            {"_id": claim_id, "status": {"$ne": "paid"}},
            {"$set": {"status": "credit_error_review_required", "error": str(exc)[:300]}})
        return
    with contextlib.suppress(Exception):
        await bot.send_message(referrer_id, fancy(
            f"🎉 **Referral Joined!**\n\n💰 You earned `₹{reward:.2f}` for a new referral. "
            "You'll also earn your first-deposit bonus when they make their first approved deposit."))
    with contextlib.suppress(Exception):
        await log_event(
            "🎁 **Referral Join Bonus Credited**\n"
            f"• Referrer: `{referrer_id}` (@{referrer.get('username') or 'N/A'})\n"
            f"• Referred: `{referred_user_id}`\n• Required channels verified: {required_chat_count}\n"
            f"• Bonus: ₹{reward:.2f}")

async def referral_first_deposit_bonus(user_id: int, amount: float):
    """% of the referred user's FIRST approved deposit (capped), claimed atomically once."""
    user_doc = await users_col.find_one({"user_id": user_id})
    referrer_id = user_doc.get("referred_by") if user_doc else None
    if not referrer_id or referrer_id == user_id:
        return
    enabled = await is_referral_enabled()
    claim = await users_col.update_one(
        {"user_id": user_id, "referral_bonus_paid": {"$ne": True}},
        {"$set": {"referral_bonus_paid": True, "referral_bonus_claimed_at": datetime.utcnow(),
                  "referral_bonus_first_deposit_amount": amount,
                  "referral_bonus_status": "processing" if enabled else "not_paid_program_disabled"}})
    if claim.modified_count != 1 or not enabled:
        return
    pct, cap = await get_referral_bonus_percent(), await get_referral_bonus_max()
    bonus = round(min(amount * (pct / 100), cap), 2)
    if bonus <= 0:
        return
    receipt = f"firstdeposit:{user_id}"
    try:
        credit = await users_col.update_one(
            {"user_id": referrer_id, "referral_deposit_credit_receipts": {"$ne": receipt}},
            {"$inc": {"balance": bonus, "withdrawable": bonus, "referral_earnings": bonus},
             "$addToSet": {"referral_deposit_credit_receipts": receipt}})
        if not credit.modified_count:
            ref_doc = await users_col.find_one({"user_id": referrer_id})
            if not ref_doc or receipt not in ref_doc.get("referral_deposit_credit_receipts", []):
                raise RuntimeError("First-deposit referrer missing before credit")
        await users_col.update_one({"user_id": user_id}, {"$set": {
            "referral_bonus_status": "paid", "referral_bonus_amount": bonus,
            "referral_bonus_referrer_id": referrer_id, "referral_bonus_paid_at": datetime.utcnow()}})
    except Exception as exc:
        log.exception(f"First-deposit referral credit failed for {user_id}")
        await users_col.update_one({"user_id": user_id}, {"$set": {
            "referral_bonus_status": "credit_error_review_required", "referral_bonus_error": str(exc)[:200]}})
        return
    with contextlib.suppress(Exception):
        await bot.send_message(referrer_id, fancy(
            f"🎉 **Referral Bonus Earned!**\n\nYour referral made their first deposit of `₹{amount}`.\n"
            f"💰 Bonus credited: `₹{bonus}`"))
    with contextlib.suppress(Exception):
        await log_event(
            "🎁 **Referral First-Deposit Bonus**\n"
            f"• Referrer: `{referrer_id}`\n• Referred: `{user_id}`\n• Deposit: ₹{amount}\n• Bonus: ₹{bonus}")

async def register_start_user(user_id: int, payload: str, sender=None) -> dict:
    """Create the user (once) with a verified referrer; never re-attach on existing users."""
    referrer_id = await resolve_referrer(payload)
    profile = {}
    if sender is not None:
        profile = {"first_name": getattr(sender, "first_name", None),
                   "last_name": getattr(sender, "last_name", None),
                   "username": getattr(sender, "username", None)}
    existing = await users_col.find_one({"user_id": user_id})
    if existing:
        if profile:
            await users_col.update_one({"user_id": user_id}, {"$set": profile})
        return existing
    if referrer_id and (referrer_id == user_id or not await users_col.find_one({"user_id": referrer_id})):
        referrer_id = None
    eligible = bool(referrer_id and await is_referral_enabled())
    user = await get_or_create_user(user_id, referrer_id)
    await users_col.update_one({"user_id": user_id, "referral_signup_eligible": {"$exists": False}},
                               {"$set": {"referral_signup_eligible": eligible, "referral_bonus_paid": False,
                                         "referral_signup_bonus_claimed": False, **profile}})
    return await users_col.find_one({"user_id": user_id}) or user

async def _ref_admin_screen():
    pct, cap = await get_referral_bonus_percent(), await get_referral_bonus_max()
    join, enabled = await get_referral_signup_bonus(), await is_referral_enabled()
    min_wd = await get_min_withdrawal()
    text = fancy(
        "🎁 **Referral Bonus Settings**\n\n"
        f"Status: {'🟢 ON' if enabled else '🔴 OFF'}\n\n"
        f"Join Bonus: **₹{join:.2f}** per eligible new referral\n"
        f"First Deposit: **{pct}%**, capped at **₹{cap}**\n"
        f"Minimum Withdrawal: **₹{min_wd}**\n\n"
        f"Example: one signup + ₹100 first deposit pays ₹{join + round(min(100 * (pct / 100), cap), 2):.2f} in total.")
    buttons = [
        [_pb("🔴 Turn OFF" if enabled else "🟢 Turn ON", "admin_toggle_referral")],
        [_pb("✏️ Edit Join Bonus", "admin_set_ref_signup"), _pb("✏️ Edit Bonus %", "admin_set_ref_percent")],
        [_pb("✏️ Edit Max Cap", "admin_set_ref_max"), _pb("✏️ Min Withdrawal", "admin_set_min_wd")],
        [_pb("◀️ Back", "asettings")],
    ]
    return text, buttons

_REF_EDITS = {
    "admin_set_ref_signup": ("referral_signup_bonus", "Join Bonus (₹)", 0, 1000),
    "admin_set_ref_percent": ("referral_bonus_percent", "First-deposit bonus %", 0, 100),
    "admin_set_ref_max": ("referral_bonus_max", "Max first-deposit bonus (₹)", 0, 100000),
    "admin_set_min_wd": ("min_withdrawal", "Minimum withdrawal (₹)", 1, 100000),
}

async def ext_referral_callback(event, data: str, user_id: int, user) -> bool:
    if data == "referral":
        if not await is_referral_enabled():
            await safe_callback_answer(event, "❌ Referral program is not available.", alert=True)
            return True
        user = user or await get_or_create_user(user_id)
        uname = await get_bot_username()
        link = f"https://t.me/{uname}?start=ref{user_id}" if uname else "N/A"
        invited = await users_col.count_documents({"referred_by": user_id})
        paid = await users_col.count_documents({"referred_by": user_id, "referral_bonus_paid": True, "referral_bonus_status": "paid"})
        join_paid = await users_col.count_documents({"referred_by": user_id, "referral_signup_bonus_status": "paid"})
        fresh = await users_col.find_one({"user_id": user_id}) or {}
        pct, cap, join = await get_referral_bonus_percent(), await get_referral_bonus_max(), await get_referral_signup_bonus()
        await event.edit(fancy(
            "🎁 **Refer & Earn**\n\n"
            f"🔗 **Your Link:**\n`{link}`\n\n"
            f"💰 **Join Bonus:** `₹{join:.2f}` after they join all required channels\n"
            f"💳 **First Deposit Bonus:** {pct}% of their **first approved deposit**, up to `₹{cap}` (extra)\n\n"
            f"👥 Total Invited: **{invited}**\n"
            f"✅ Join Bonuses Paid: **{join_paid}**\n"
            f"💳 First-Deposit Bonuses: **{paid}**\n"
            f"💰 Total Earned: `₹{float(fresh.get('referral_earnings', 0)):.2f}`\n\n"
            f"💸 Withdrawable: `₹{float(fresh.get('withdrawable', 0)):.2f}`\n"
            f"📏 Minimum Withdrawal: `₹{await get_min_withdrawal()}`"),
            buttons=[
                [url_btn("Share Link", f"https://t.me/share/url?url={link}&text=Buy+Telegram+accounts+instantly!", "success")],
                [_pb("💸 Withdraw", "withdraw"), _pb("📜 Withdrawal History", "my_withdrawals")],
                [_pb("🏠 Home", "main_menu")],
            ])
        await safe_callback_answer(event)
        return True

    if data == "admin_referral_settings" or data == "admin_toggle_referral" or data in _REF_EDITS:
        if not await is_admin(user_id):
            await safe_callback_answer(event, "❌ Unauthorized", alert=True)
            return True
        if data == "admin_toggle_referral":
            await _ref_set("referral_enabled", not await is_referral_enabled())
        elif data in _REF_EDITS:
            key, label, lo, hi = _REF_EDITS[data]
            user_states[user_id] = {"action": "ref_edit", "key": key, "label": label, "lo": lo, "hi": hi}
            await event.edit(fancy(f"✏️ **Edit {label}**\n\nSend the new value ({lo} – {hi})."),
                             buttons=[[_pb("❌ Cancel", "admin_referral_settings")]])
            await safe_callback_answer(event)
            return True
        text, buttons = await _ref_admin_screen()
        await _edit_quiet(event, text, buttons)
        await safe_callback_answer(event)
        return True

    # ── withdrawals (referral earnings) ──
    if data == "withdraw":
        user = await users_col.find_one({"user_id": user_id}) or {}
        avail, min_wd = float(user.get("withdrawable", 0)), await get_min_withdrawal()
        if avail < min_wd:
            await safe_callback_answer(event, f"Minimum withdrawal is ₹{min_wd}. You have {avail:.2f} withdrawable.", alert=True)
            return True
        user_states[user_id] = {"action": "wd_amount"}
        await event.edit(fancy(
            f"💸 **Withdraw**\n\nWithdrawable: `₹{avail:.2f}`\nMinimum: `₹{min_wd}`\n\nSend the amount to withdraw:"),
            buttons=[[_pb("❌ Cancel", "referral")]])
        await safe_callback_answer(event)
        return True
    if data == "my_withdrawals":
        rows = await withdrawals_col.find({"user_id": user_id}).sort("created_at", -1).to_list(10)
        body = "\n".join(f"• `₹{r['amount']}` — {r['status']} — {r['created_at'].strftime('%d/%m %H:%M')}" for r in rows) or "No withdrawals yet."
        await event.edit(fancy(f"📜 **Withdrawal History**\n\n{body}"), buttons=[[_pb("◀️ Back", "referral")]])
        await safe_callback_answer(event)
        return True
    if data.startswith(("wd_approve:", "wd_reject:")):
        if not await is_admin(user_id):
            await safe_callback_answer(event, "❌ Access denied.", alert=True)
            return True
        approve = data.startswith("wd_approve:")
        try:
            wid = ObjectId(data.split(":", 1)[1])
        except Exception:
            return True
        w = await withdrawals_col.find_one_and_update(
            {"_id": wid, "status": "pending"},
            {"$set": {"status": "approved" if approve else "rejected", "handled_by": user_id, "handled_at": datetime.utcnow()}})
        if not w:
            await safe_callback_answer(event, "⚠️ Already processed.", alert=True)
            return True
        if not approve:      # rejected → money goes back to the wallet
            await users_col.update_one({"user_id": w["user_id"]}, {"$inc": {"balance": w["amount"], "withdrawable": w["amount"]}})
        with contextlib.suppress(Exception):
            await bot.send_message(w["user_id"], fancy(
                f"✅ **Withdrawal approved**\n`₹{w['amount']}` will be paid to `{w['upi']}`." if approve else
                f"❌ **Withdrawal rejected**\n`₹{w['amount']}` returned to your wallet."))
        await _edit_quiet(event, fancy(f"{'✅ Approved' if approve else '❌ Rejected'} withdrawal `₹{w['amount']}` → `{w['upi']}` (user `{w['user_id']}`)"), None)
        return True
    return False

async def ext_referral_message(event, user_id: int, st: dict) -> bool:
    action = st.get("action")
    text = (event.message.text or "").strip()
    if action == "ref_edit":
        if not await is_admin(user_id):
            user_states.pop(user_id, None)
            return True
        try:
            val = round(float(text), 2)
            assert st["lo"] <= val <= st["hi"]
        except Exception:
            await event.respond(fancy(f"❌ Send a number between {st['lo']} and {st['hi']}."))
            return True
        await _ref_set(st["key"], val)
        user_states.pop(user_id, None)
        t, b = await _ref_admin_screen()
        await event.respond(t, buttons=b)
        return True
    if action == "wd_amount":
        user = await users_col.find_one({"user_id": user_id}) or {}
        avail, min_wd = float(user.get("withdrawable", 0)), await get_min_withdrawal()
        try:
            amt = round(float(text), 2)
            assert min_wd <= amt <= avail
        except Exception:
            await event.respond(fancy(f"❌ Send an amount between {min_wd} and {avail:.2f}."))
            return True
        st.update(action="wd_upi", amount=amt)
        await event.respond(fancy("Send your **UPI ID** for the payout:"), buttons=[[_pb("❌ Cancel", "referral")]])
        return True
    if action == "wd_upi":
        if "@" not in text or len(text) > 60:
            await event.respond(fancy("❌ Send a valid UPI ID (like name@bank)."))
            return True
        amt = st["amount"]
        taken = await users_col.update_one(
            {"user_id": user_id, "withdrawable": {"$gte": amt}, "balance": {"$gte": amt}},
            {"$inc": {"balance": -amt, "withdrawable": -amt}})
        user_states.pop(user_id, None)
        if not taken.modified_count:
            await event.respond(fancy("❌ Your withdrawable balance changed. Try again."))
            return True
        res = await withdrawals_col.insert_one({"user_id": user_id, "amount": amt, "upi": text,
                                                "status": "pending", "created_at": datetime.utcnow()})
        await event.respond(fancy(f"✅ **Withdrawal requested**\n`₹{amt}` → `{text}`\nAn admin will review it soon."),
                            buttons=[[_pb("🏠 Home", "main_menu")]])
        msg = fancy(f"💸 **Withdrawal Request**\n\n• User: `{user_id}`\n• Amount: `₹{amt}`\n• UPI: `{text}`")
        btns = [[_pb("✅ Approve", f"wd_approve:{res.inserted_id}"), _pb("❌ Reject", f"wd_reject:{res.inserted_id}")]]
        sent = False
        group = await _payment_group()
        for target in ([group] if group else []) + await get_all_admin_ids():
            with contextlib.suppress(Exception):
                await bot.send_message(target, msg, buttons=btns)
                sent = True
                if group and target == group:
                    break
        return True
    return False


# ── 27.7 PAYMENT CONTROL · RAZORPAY API VERIFICATION · PAYMENT GROUP ──
from urllib.parse import urlsplit

async def _pay_set(key: str, default=None):
    doc = await settings_col.find_one({"key": key})
    return doc.get("value", default) if doc else default

async def _pay_put(key: str, value):
    await settings_col.update_one({"key": key}, {"$set": {"value": value, "updated_at": datetime.utcnow()}}, upsert=True)
    _settings_cache.pop(key, None) if "_settings_cache" in globals() else None
    if key == "force_join_channels":
        global _fj_cache
        _fj_cache = (0.0, None)

def _as_bool(v, default=True) -> bool:
    if v is None:
        return default
    if isinstance(v, str):
        return v.strip().lower() in ("1", "true", "yes", "on")
    return bool(v)

async def reload_razorpay_keys():
    """Admin-panel keys override the .env ones; the existing Razorpay helpers read these globals."""
    global RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET, RAZORPAY_WEBHOOK_SECRET
    kid = str(await _pay_set("razorpay_key_id", "") or "").strip()
    sec = str(await _pay_set("razorpay_key_secret", "") or "").strip()
    whs = str(await _pay_set("razorpay_webhook_secret", "") or "").strip()
    if kid and sec:
        RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET = kid, sec
    if whs:
        RAZORPAY_WEBHOOK_SECRET = whs

def validate_payment_link(raw: str) -> str:
    """HTTPS only — never put arbitrary schemes behind a Telegram button."""
    value = str(raw or "").strip()
    if not value or len(value) > 2048 or any(ch.isspace() for ch in value):
        raise ValueError("Send one valid HTTPS payment link (max 2048 characters).")
    parsed = urlsplit(value)
    if (parsed.scheme.lower() != "https" or not parsed.hostname
            or parsed.username is not None or parsed.password is not None):
        raise ValueError("Payment links must start with https:// and contain a valid host.")
    return value

async def get_deposit_method_availability() -> dict:
    rz = bool(RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET)
    manual_on = _as_bool(await _pay_set("manual_payment_enabled", True))
    upi = bool(await get_setting("upi_id")) and manual_on
    link = bool(await _pay_set("manual_payment_link", "")) and manual_on
    return {
        "rz_qr": rz and _as_bool(await _pay_set("pay_rz_qr_enabled", True)),
        "rz_link": rz and _as_bool(await _pay_set("pay_rz_link_enabled", True)),
        "manual": upi, "mlink": link, "manual_enabled": manual_on,
    }

async def _deposit_method_rows(prefix: str, suffix: str = "") -> list:
    av = await get_deposit_method_availability()
    rows = []
    if av["rz_qr"]:
        rows.append([color_btn("UPI · Automatic (QR)", f"{prefix}auto{suffix}", "default")])
    if av["rz_link"]:
        rows.append([color_btn("Razorpay Payment Link (Auto)", f"{prefix}link{suffix}", "default")])
    if av["manual"]:
        rows.append([color_btn("UPI · Manual (QR + Screenshot)", f"{prefix}manual{suffix}", "default")])
    if av["mlink"]:
        rows.append([color_btn("Payment Link + Screenshot", f"{prefix}mlink{suffix}", "default")])
    return rows

# ── strict Razorpay verification (IDs / amounts are never taken from the user) ──
async def razorpay_api_get(path: str):
    if not (RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET):
        raise RuntimeError("Razorpay API keys are not configured")
    async with aiohttp.ClientSession(auth=aiohttp.BasicAuth(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET)) as s:
        async with s.get(f"{RAZORPAY_API_BASE}{path}", timeout=aiohttp.ClientTimeout(total=15)) as r:
            if r.status != 200:
                log.error(f"Razorpay API GET {path.split('?')[0]} returned HTTP {r.status}")
                raise RuntimeError("Razorpay API temporarily unavailable")
            return await r.json(content_type=None)

async def _api_verify_razorpay_deposit(dep: dict):
    """-> (payment_id | None, reason). Exactly one captured payment of the exact amount."""
    paise = expected_paise(dep.get("amount"))
    if not paise:
        return None, "Invalid deposit amount; contact support."
    method = dep.get("method")
    if method == "razorpay_auto":
        qr_id = dep.get("qr_code_id")
        if not isinstance(qr_id, str) or not re.fullmatch(r"qr_[A-Za-z0-9]+", qr_id):
            return None, "Invalid QR reference."
        ids = qr_payment_ids(await razorpay_api_get(f"/payments/qr_codes/{qr_id}/payments?count=100"), paise)
    elif method == "razorpay_link":
        link_id = dep.get("payment_link_id")
        if not isinstance(link_id, str) or not re.fullmatch(r"plink_[A-Za-z0-9]+", link_id):
            return None, "Invalid Payment Link reference."
        ids = link_payment_ids(await razorpay_api_get(f"/payment_links/{link_id}"), link_id, str(dep["_id"]), paise)
    else:
        return None, "Not a Razorpay API-verifiable deposit."
    if len(ids) != 1 or len(set(ids)) != 1:
        return None, "Payment not captured yet, or needs manual reconciliation."
    payment = await razorpay_api_get(f"/payments/{ids[0]}")
    if not captured_payment(payment, ids[0], paise):
        return None, "Payment is not captured for this amount."
    return ids[0], None

async def razorpay_deposit_paid(dep: dict):
    """Returns the verified payment id (truthy) or None; never raises."""
    try:
        pid, _ = await _api_verify_razorpay_deposit(dep)
        return pid
    except Exception as e:
        log.warning(f"[Razorpay] verify failed for {dep.get('_id')}: {e}")
        return None

async def razorpay_create_payment_link(amount: float, dep_id: str, user_id: int) -> Optional[dict]:
    if not (RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET):
        return None
    payload = {
        "amount": int(round(amount * 100)), "currency": "INR", "accept_partial": False,
        "expire_by": int(time.time()) + max(1200, RAZORPAY_QR_EXPIRY_SECONDS),
        "reference_id": f"dep_{dep_id}", "description": f"Wallet top-up for user {user_id}",
        "notes": {"deposit_id": str(dep_id), "user_id": str(user_id)},
        "notify": {"sms": False, "email": False}, "reminder_enable": False,
    }
    try:
        async with aiohttp.ClientSession(auth=aiohttp.BasicAuth(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET)) as s:
            async with s.post(f"{RAZORPAY_API_BASE}/payment_links", json=payload,
                              timeout=aiohttp.ClientTimeout(total=15)) as r:
                body = await r.json(content_type=None)
                if r.status not in (200, 201):
                    log.error(f"Razorpay Payment Link create failed [{r.status}]: {body}")
                    err = (body.get("error") or {}) if isinstance(body, dict) else {}
                    await log_event(f"⚠️ **Razorpay Payment Link failed**\n• HTTP {r.status}: `{err.get('description') or err.get('code') or str(body)[:150]}`")
                    return None
                return body
    except Exception as e:
        log.error(f"Razorpay Payment Link create error: {e}")
        return None

async def ext_close_deposit_source(dep: dict):
    """Cancel/close the Razorpay QR or Payment Link of a cancelled deposit."""
    if not dep:
        return
    if dep.get("qr_code_id"):
        await razorpay_close_qr(dep["qr_code_id"])
    link_id = dep.get("payment_link_id")
    if link_id and RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET:
        try:
            async with aiohttp.ClientSession(auth=aiohttp.BasicAuth(RAZORPAY_KEY_ID, RAZORPAY_KEY_SECRET)) as s:
                async with s.post(f"{RAZORPAY_API_BASE}/payment_links/{link_id}/cancel",
                                  timeout=aiohttp.ClientTimeout(total=10)):
                    pass
        except Exception as e:
            log.warning(f"[Razorpay] payment link cancel failed for {link_id}: {e}")

# ── payment group (manual proofs + auto-payment notices) ──
async def send_deposit_proof(photo_bytes, user_id: int, amount: float, credits, txn_id: str, dep_id: str, kind="MANUAL"):
    """Post the proof to the payment group (fallback: every admin's DM). Returns True if delivered."""
    name = await get_display_name(user_id)
    caption = fancy(
        f"📸 **New Deposit Request**\n"
        f"• Method: `{kind}`\n• User: {name}\n• User ID: `{user_id}`\n"
        f"• Amount: `₹{amount:.2f}`\n• Added: `+₹{credits}`\n• Txn Ref: `{txn_id}`\n• Deposit ID: `{dep_id}`")
    buttons = [[color_btn("✅ Approve", f"dep_approve:{dep_id}:{user_id}:{amount}", "default"),
                color_btn("❌ Reject", f"dep_reject:{dep_id}:{user_id}", "default")]]
    group = await _payment_group()
    targets = [group] if group else await get_all_admin_ids()
    delivered = False
    for t in targets:
        for attempt in range(3):
            try:
                if photo_bytes:
                    f = io.BytesIO(photo_bytes)
                    f.name = "payment_proof.jpg"
                    sent = await bot.send_file(t, f, caption=caption, buttons=buttons)
                else:
                    sent = await bot.send_message(t, caption, buttons=buttons)
                delivered = True
                if group and t == group:
                    await deposits_col.update_one({"_id": ObjectId(dep_id)},
                                                  {"$set": {"payment_group_message_id": sent.id}})
                break
            except Exception as e:
                log.warning(f"[deposit proof] send to {t} failed (try {attempt + 1}): {e}")
                await asyncio.sleep(1.0)
    return delivered

async def notify_payment_group_auto(user_id: int, amount: float, dep_id: str, method_label: str):
    group = await _payment_group()
    if not group:
        return
    with contextlib.suppress(Exception):
        await bot.send_message(group, fancy(
            "⚡ **Auto Payment Started**\n\n"
            f"• User: {await get_display_name(user_id)}\n• User ID: `{user_id}`\n"
            f"• Amount: `₹{amount:.2f}`\n• Method: `{method_label}`\n• Deposit ID: `{dep_id}`\n\n"
            "⏳ Waiting for Razorpay confirmation (API-verified)."))

async def sync_payment_group_message(dep: dict, status_text: str):
    group = await _payment_group()
    msg_id = (dep or {}).get("payment_group_message_id")
    if not group or not msg_id:
        return
    with contextlib.suppress(Exception):
        msg = await bot.get_messages(group, ids=int(msg_id))
        base = (msg.text or msg.message or "") if msg else ""
        if base and not any(k in base for k in ("APPROVED", "REJECTED", "CANCELLED")):
            await bot.edit_message(group, int(msg_id), base.rstrip() + "\n\n" + status_text, buttons=None)

# ── deposit starters for the two new methods ──
async def _start_razorpay_link_deposit(event, user_id: int, amount: float, credits: int):
    if not (RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET):
        await event.answer("❌ Razorpay is not set up yet.", alert=True)
        return
    blocking = await _blocking_pending_deposit(user_id)
    if blocking:
        await _show_pending_deposit_block(event, blocking)
        return
    with contextlib.suppress(Exception):
        await event.edit("Creating your payment link…")
    dep = await deposits_col.insert_one({"user_id": user_id, "amount": amount, "credits": credits,
                                         "method": "razorpay_link", "status": "pending", "created_at": datetime.utcnow()})
    dep_id = str(dep.inserted_id)
    link = await razorpay_create_payment_link(amount, dep_id, user_id)
    if not link or not link.get("id") or not link.get("short_url"):
        await deposits_col.update_one({"_id": dep.inserted_id}, {"$set": {"status": "failed"}})
        await event.edit(fancy("❌ **Could not create the payment link.**\n\nPlease try another method."),
                         buttons=[[color_btn("◀️ Back", "deposit", "default")]])
        return
    await deposits_col.update_one({"_id": dep.inserted_id}, {"$set": {
        "payment_link_id": link["id"], "payment_link_url": link["short_url"], "ui_msg_id": event.message_id}})
    user_states[user_id] = {"deposit_id_obj": dep_id, "credits": credits, "amount": amount, "ui_msg_id": event.message_id}
    await event.edit(fancy(
        "🔗 **Pay with Razorpay link**\n\n"
        f"• Amount: `₹{amount:.2f}`\n\n"
        "Open the link, pay the exact amount, then your wallet is credited automatically "
        "after Razorpay confirms it. You can also tap Check Payment.\n\n💫 Valid for 20 minutes."),
        buttons=[[url_btn("Pay Now", link["short_url"], "success")],
                 [color_btn("✅ Check Payment", "check_payment", "default")],
                 [color_btn("❌ Cancel", "cancel_payment", "default")]])
    await notify_payment_group_auto(user_id, amount, dep_id, "Razorpay Payment Link")

async def _start_manual_link_deposit(event, user_id: int, amount: float, credits: int):
    url = str(await _pay_set("manual_payment_link", "") or "")
    if not url:
        await event.answer("❌ Payment link is not configured.", alert=True)
        return
    blocking = await _blocking_pending_deposit(user_id)
    if blocking:
        await _show_pending_deposit_block(event, blocking)
        return
    txn_id = f"DEP{datetime.utcnow().strftime('%y%m%d%H%M')}{uuid.uuid4().hex[:4].upper()}"
    dep = await deposits_col.insert_one({"user_id": user_id, "amount": amount, "credits": credits,
                                         "method": "manual_link", "txn_id": txn_id, "status": "pending",
                                         "created_at": datetime.utcnow()})
    user_states[user_id] = {"state": "await_deposit_screenshot", "credits": credits, "amount": amount,
                            "txn_id": txn_id, "ui_msg_id": event.message_id, "deposit_id_obj": str(dep.inserted_id),
                            "kind": "PAYMENT LINK"}
    await event.edit(fancy(
        "🔗 **Payment Link Deposit**\n\n"
        f"• Amount: `₹{amount:.2f}`\n• Txn Ref: `{txn_id}`\n\n"
        "Open the link and pay the exact amount, then send the payment screenshot here — "
        "an admin will verify and approve it."),
        buttons=[[url_btn("Open Payment Link", url, "success")],
                 [color_btn("❌ Cancel", "cancel_payment", "default")],
                 [color_btn("◀️ Back", "deposit", "default")]])

async def ext_start_deposit_method(event, user_id: int, method: str, amount: float, credits: int):
    av = await get_deposit_method_availability()
    key = {"auto": "rz_qr", "link": "rz_link", "manual": "manual", "mlink": "mlink"}.get(method)
    if not key or not av.get(key):
        await event.answer("❌ This payment method is currently unavailable.", alert=True)
        return
    if method == "auto":
        await _start_razorpay_auto_deposit(event, user_id, amount, credits)
    elif method == "link":
        await _start_razorpay_link_deposit(event, user_id, amount, credits)
    elif method == "manual":
        await _start_manual_deposit(event, user_id, amount, credits)
    else:
        await _start_manual_link_deposit(event, user_id, amount, credits)

async def _show_method_picker(target, user_id: int, amount: float, credits: int, *, edit: bool):
    rows = await _deposit_method_rows("pay_method_custom:")
    user_states[user_id] = {"custom_amount": amount, "custom_credits": credits}
    if not rows:
        text, btns = fancy("⚠️ **No payment method is available right now.**\n\nPlease contact support."), [[color_btn("Back", "balance", "default")]]
    else:
        text = fancy(f"💳 **Select Payment Method**\n\nAmount: `₹{amount:.2f}`")
        btns = rows + [[color_btn("Back", "deposit_pkgs", "default")]]
    await (target.edit if edit else target.respond)(text, buttons=btns)

async def ext_payments_callback(event, data: str, user_id: int) -> bool:
    if data == "deposit":
        user_states.pop(user_id, None)
        rows = await _deposit_method_rows("dep_upi:")
        rows.append([color_btn("Deposit Packages", "deposit_pkgs", "default")])
        rows.append([color_btn("Back", "balance", "default")])
        await event.edit(RAW + "**ADD FUNDS**\n\n" + f"{LINE}\n" + "Select a deposit method:\n" + f"{LINE}", buttons=rows)
        return True
    if data.startswith("dep_upi:"):
        method = data.split(":", 1)[1]
        av = await get_deposit_method_availability()
        if not av.get({"auto": "rz_qr", "link": "rz_link", "manual": "manual", "mlink": "mlink"}.get(method, ""), False):
            await event.answer("❌ This payment method is currently unavailable.", alert=True)
            return True
        min_d, max_d = await _deposit_limits()
        user_states[user_id] = {"state": "custom_deposit", "prompt_id": event.message_id, "method": method}
        title = {"auto": "UPI · AUTOMATIC", "link": "RAZORPAY LINK", "manual": "UPI · MANUAL", "mlink": "PAYMENT LINK"}[method]
        await event.edit(RAW + f"**{title}**\n\nEnter the amount you want to deposit (₹):\n\n"
                         f"Minimum : ₹{min_d:g}\nMaximum : ₹{max_d:g}",
                         buttons=[[color_btn("Cancel", "dep_cancel", "default")]])
        return True
    if data.startswith("pkg:"):
        credits = int(data.split(":")[1])
        pkg = await packages_col.find_one({"credits": credits})
        if not pkg:
            await event.answer("❌ Package not found.", alert=True)
            return True
        await _show_method_picker(event, user_id, float(pkg["price"]), credits, edit=True)
        return True
    if data.startswith("pay_method:"):
        _, method, credits_str = data.split(":")
        pkg = await packages_col.find_one({"credits": int(credits_str)})
        if not pkg:
            await event.answer("❌ Package error.", alert=True)
            return True
        await ext_start_deposit_method(event, user_id, method, float(pkg["price"]), int(credits_str))
        return True
    if data.startswith("pay_method_custom:"):
        method = data.split(":", 1)[1]
        st = user_states.get(user_id, {})
        if st.get("custom_amount") is None or st.get("custom_credits") is None:
            await event.answer("❌ No active deposit. Start again.", alert=True)
            return True
        await ext_start_deposit_method(event, user_id, method, st["custom_amount"], st["custom_credits"])
        return True
    return False

async def ext_payments_message(event, user_id: int, state_data: dict) -> bool:
    """Custom amount typed → continue with the chosen method (or show the picker)."""
    if state_data.get("state") != "custom_deposit":
        return False
    text = (event.message.text or "").strip()
    try:
        amount = float(text.replace(",", ""))
    except ValueError:
        await event.respond("Please send a valid number.")
        return True
    min_d, max_d = await _deposit_limits()
    if amount < min_d:
        await event.respond(f"Minimum deposit is ₹{min_d:g}.")
        return True
    if amount > max_d:
        await event.respond(f"Maximum deposit is ₹{max_d:g}.")
        return True
    credits = int(amount // 1)
    method = state_data.get("method")
    await _delete_msg(user_id, state_data.get("prompt_id"))
    with contextlib.suppress(Exception):
        await event.delete()
    if method:
        user_states.pop(user_id, None)
        msg = await event.respond("Creating your payment…")
        await ext_start_deposit_method(_MsgUI(msg, user_id), user_id, method, amount, credits)
        return True
    await _show_method_picker(event, user_id, amount, credits, edit=False)
    return True

# ── admin: Payment Control ──
async def _pay_admin_screen():
    av = await get_deposit_method_availability()
    link = str(await _pay_set("manual_payment_link", "") or "")
    upi = await get_setting("upi_id") or "—"
    payee = await get_setting("upi_name") or "—"
    rz = bool(RAZORPAY_KEY_ID and RAZORPAY_KEY_SECRET)
    on = lambda b: "🟢 ON" if b else "🔴 OFF"
    text = fancy(
        "💳 **Payment Control**\n\n"
        f"• Razorpay keys: {'✅ set' if rz else '❌ missing'}\n"
        f"• Razorpay QR (auto): {on(_as_bool(await _pay_set('pay_rz_qr_enabled', True)))}\n"
        f"• Razorpay Payment Link (auto): {on(_as_bool(await _pay_set('pay_rz_link_enabled', True)))}\n"
        f"• Manual payments (UPI QR + link): {on(av['manual_enabled'])}\n"
        f"• UPI ID: `{upi}`  • Payee: `{payee}`\n"
        f"• Manual payment link: `{link or 'not set'}`\n"
        f"• Webhook: {on(RAZORPAY_ENABLE_WEBHOOK)} (API polling every {RAZORPAY_API_POLL_SECONDS}s works without it)\n\n"
        "Users only see the methods that are ON and configured.")
    btn = lambda t, d: color_btn(t, d, "default")
    buttons = [
        [btn("Razorpay QR " + ("OFF" if _as_bool(await _pay_set('pay_rz_qr_enabled', True)) else "ON"), "admin_pay_toggle:pay_rz_qr_enabled"),
         btn("Razorpay Link " + ("OFF" if _as_bool(await _pay_set('pay_rz_link_enabled', True)) else "ON"), "admin_pay_toggle:pay_rz_link_enabled")],
        [btn("Manual " + ("OFF" if av["manual_enabled"] else "ON"), "admin_pay_toggle:manual_payment_enabled")],
        [btn("✏️ UPI ID", "admin_pay_edit:upi_id"), btn("✏️ Payee Name", "admin_pay_edit:upi_name")],
        [btn("🔗 Set Payment Link", "admin_pay_edit:manual_payment_link"), btn("🗑️ Clear Link", "admin_pay_clearlink")],
        [btn("🔑 Razorpay Keys", "admin_pay_keys"), btn("🧪 Test Razorpay", "admin_pay_test")],
        [btn("◀️ Back", "asettings")],
    ]
    return text, buttons

_PAY_EDITS = {
    "upi_id": "UPI ID (like name@bank)",
    "upi_name": "payee name",
    "manual_payment_link": "HTTPS payment link",
    "razorpay_key_id": "Razorpay Key ID",
    "razorpay_key_secret": "Razorpay Key Secret",
    "razorpay_webhook_secret": "Razorpay Webhook Secret (send `-` to clear)",
}

async def ext_payments_admin_callback(event, data: str, user_id: int) -> bool:
    if data == "admin_pay_test":
        if not await is_admin(user_id):
            await safe_callback_answer(event, "❌ Unauthorized", alert=True)
            return True
        await safe_callback_answer(event, "Testing…")
        try:
            await razorpay_api_get("/payments/qr_codes?count=1")
            msg = "✅ Keys are valid and the QR Codes API answered."
        except Exception as e:
            msg = f"❌ {e}"
        # also try creating a real (tiny) QR so feature-not-enabled errors show up
        qr = await razorpay_create_qr(1, "test", user_id)
        if qr and qr.get("id"):
            await razorpay_close_qr(qr["id"])
            msg += "\n✅ QR creation works."
        else:
            msg += f"\n❌ QR creation failed: `{_RZ_LAST_ERROR or 'unknown'}`"
            msg += "\n\nIf it says QR codes are not enabled, ask Razorpay to activate UPI QR on your account, or turn on the Razorpay Payment Link method instead."
        await event.respond(fancy("🧪 **Razorpay test**\n\n" + msg),
                            buttons=[[color_btn("◀️ Back", "admin_payment_options", "default")]])
        return True
    if not (data in ("admin_payment_options", "admin_pay_clearlink", "admin_pay_keys")
            or data.startswith(("admin_pay_toggle:", "admin_pay_edit:"))):
        return False
    if not await is_admin(user_id):
        await safe_callback_answer(event, "❌ Unauthorized", alert=True)
        return True
    if data.startswith("admin_pay_toggle:"):
        key = data.split(":", 1)[1]
        if key in ("pay_rz_qr_enabled", "pay_rz_link_enabled", "manual_payment_enabled"):
            await _pay_put(key, not _as_bool(await _pay_set(key, True)))
    elif data == "admin_pay_clearlink":
        await _pay_put("manual_payment_link", "")
    elif data == "admin_pay_keys":
        kid = str(await _pay_set("razorpay_key_id", "") or RAZORPAY_KEY_ID or "")
        masked = (kid[:8] + "…" + kid[-3:]) if len(kid) > 12 else (kid or "not set")
        await event.edit(fancy(
            "🔑 **Razorpay Keys**\n\n"
            f"• Key ID: `{masked}`\n• Secret: {'✅ set' if RAZORPAY_KEY_SECRET else '❌ not set'}\n"
            f"• Webhook secret: {'✅ set' if RAZORPAY_WEBHOOK_SECRET else '— (not needed for API polling)'}\n\n"
            "Keys saved here override the .env values instantly. Your message with a secret is deleted after saving."),
            buttons=[[color_btn("✏️ Key ID", "admin_pay_edit:razorpay_key_id"), color_btn("✏️ Key Secret", "admin_pay_edit:razorpay_key_secret")],
                     [color_btn("✏️ Webhook Secret", "admin_pay_edit:razorpay_webhook_secret")],
                     [color_btn("◀️ Back", "admin_payment_options")]])
        await safe_callback_answer(event)
        return True
    elif data.startswith("admin_pay_edit:"):
        key = data.split(":", 1)[1]
        if key not in _PAY_EDITS:
            return True
        user_states[user_id] = {"action": "pay_edit", "key": key}
        await event.edit(fancy(f"✏️ **Edit {_PAY_EDITS[key]}**\n\nSend the new value."),
                         buttons=[[color_btn("❌ Cancel", "admin_payment_options", "default")]])
        await safe_callback_answer(event)
        return True
    text, buttons = await _pay_admin_screen()
    await _edit_quiet(event, text, buttons)
    await safe_callback_answer(event)
    return True

async def ext_payments_admin_message(event, user_id: int, st: dict) -> bool:
    if st.get("action") != "pay_edit":
        return False
    if not await is_admin(user_id):
        user_states.pop(user_id, None)
        return True
    key, raw = st["key"], (event.message.text or "").strip()
    secret = key.startswith("razorpay_")
    try:
        if key == "manual_payment_link":
            raw = validate_payment_link(raw)
        elif key == "razorpay_webhook_secret" and raw == "-":
            raw = ""
        elif not raw or len(raw) > 200:
            raise ValueError("Send a valid value (max 200 characters).")
        elif key == "upi_id" and "@" not in raw:
            raise ValueError("A UPI ID looks like name@bank.")
    except ValueError as e:
        await event.respond(fancy(f"❌ {e}"))
        return True
    if key in ("upi_id", "upi_name"):
        await set_setting(key, raw)
    else:
        await _pay_put(key, raw)
    if secret:
        await reload_razorpay_keys()
        with contextlib.suppress(Exception):
            await event.delete()          # never leave API secrets in the chat
    user_states.pop(user_id, None)
    text, buttons = await _pay_admin_screen()
    await event.respond(fancy("✅ Saved.\n\n") + text, buttons=buttons)
    return True


# ── 27.8 ADMIN SETTINGS · LOG CHANNELS · FORCE JOIN · SERVER 3 MARKUP ──
_fj_cache = (0.0, None)
async def get_force_join_chats() -> list:
    """Channels from .env plus the ones added from the admin panel (deduplicated)."""
    global _fj_cache
    if _fj_cache[1] is not None and time.time() - _fj_cache[0] < 30:
        return list(_fj_cache[1])
    stored = await _pay_set("force_join_channels", []) or []
    out, seen = [], set()
    for raw in list(RAW_CHAT_IDS) + [str(x) for x in stored]:
        raw = str(raw).strip()
        if raw and raw.lower() not in seen:
            seen.add(raw.lower())
            out.append(raw)
    _fj_cache = (time.time(), list(out))
    return out

async def _channel_label(raw) -> str:
    try:
        parsed = _parse_chat_id(str(raw))
        ent = await bot.get_entity(parsed) if parsed is not None else None
        return getattr(ent, "title", None) or str(raw)
    except Exception:
        return str(raw)

async def _channels_screen():
    private = LOGS_CHANNEL_ID or int(await get_setting("logs_channel_id", 0) or 0)
    public = await _public_log_channel()
    ann = await _announcement_channel()
    pay = await _payment_group()
    text = fancy(
        "📢 **Channels & Logs**\n\n"
        f"• 🔒 Private logs: `{private or 'Not set'}`\n"
        "   (purchases, deposits, OTPs, referral credits, safety alerts)\n"
        f"• 🌐 Public purchase feed: `{public or 'Not set'}`\n"
        "   (masked user IDs / numbers only)\n"
        f"• 📦 Stock announcements: `{ann or 'Not set'}`\n"
        f"• 💳 Payment review group: `{pay or 'Not set'}`\n"
        "   (manual proofs + Approve / Reject buttons)\n\n"
        "Add the bot as an admin in each chat, then set its ID (like -1001234567890).")
    b = lambda t, d: color_btn(t, d, "default")
    return text, [
        [b("🔒 Private Logs", "set_logs_channel"), b("🌐 Public Feed", "admin_chan_edit:public_log_channel_id")],
        [b("📦 Announcements", "admin_chan_edit:announcement_channel_id"), b("💳 Payment Group", "admin_chan_edit:payment_group_id")],
        [b("🧪 Send Test Messages", "admin_chan_test")],
        [b("◀️ Back", "asettings")],
    ]

async def _force_join_screen():
    env_list = set(x.lower() for x in RAW_CHAT_IDS)
    chats = await get_force_join_chats()
    lines = []
    for c in chats:
        lines.append(f"• {await _channel_label(c)} (`{c}`)" + (" — .env" if c.lower() in env_list else ""))
    ex_n = len(await _fj_exempt())
    text = fancy("🛡️ **Force Join**\n\nUsers must be members of all of these before using the bot "
                 "(and before a referral join bonus is paid):\n\n" + ("\n".join(lines) or "None configured.")
                 + f"\n\n✅ Approved users (no join needed): `{ex_n}`")
    b = lambda t, d: color_btn(t, d, "default")
    rows = [[b("➕ Add Channel / Group", "admin_fj_add")],
            [b("✅ Approve User (skip join)", "admin_fj_ap_add")]]
    for uid_ in sorted(await _fj_exempt()):
        rows.append([b(f"🚫 Remove approval {uid_}", f"admin_fj_ap_rm:{uid_}")])
    stored = await _pay_set("force_join_channels", []) or []
    for i, c in enumerate(stored):
        rows.append([b(f"🗑️ Remove {str(c)[:24]}", f"admin_fj_rm:{i}")])
    rows.append([b("◀️ Back", "asettings")])
    return text, rows

async def _server3_admin_screen():
    mk = await server3_server.get_markup_percent()
    active = await _server_active(SERVER3_NUMBER)
    text = fancy(
        "🌐 **Server 3 (Heart TG Store)**\n\n"
        f"• API: {'✅ Connected' if server3_server.configured else '❌ SERVER3_API_KEY missing (.env)'}\n"
        f"• Visible to users: {'🟢 On' if active else '🔴 Off'}\n"
        f"• Markup on supplier price: `{mk}%`\n"
        f"• Provider 1 / Provider 2 prices are live; refunds are mirrored back to the wallet automatically.")
    b = lambda t, d: color_btn(t, d, "default")
    return text, [[b("📈 Edit Markup %", "admin_server3_markup")],
                  [b("🔌 Toggle Server 3", "admin_server3_toggle")],
                  [b("◀️ Back", "asettings")]]

async def ext_admin_callback(event, data: str, user_id: int) -> bool:
    if not (data in ("admin_channels", "admin_chan_test", "admin_force_join", "admin_fj_add", "admin_fj_ap_add",
                     "admin_server3", "admin_server3_markup", "admin_server3_toggle")
            or data.startswith(("admin_chan_edit:", "admin_fj_rm:", "admin_fj_ap_rm:"))):
        return False
    if not await is_admin(user_id):
        await safe_callback_answer(event, "❌ Unauthorized", alert=True)
        return True
    if data == "admin_channels":
        t, b = await _channels_screen()
        await _edit_quiet(event, t, b)
    elif data.startswith("admin_chan_edit:"):
        key = data.split(":", 1)[1]
        user_states[user_id] = {"action": "chan_edit", "key": key}
        await event.edit(fancy("✏️ **Set channel / group ID**\n\nSend the chat ID (like `-1001234567890`) or `0` to disable."),
                         buttons=[[color_btn("❌ Cancel", "admin_channels", "default")]])
    elif data == "admin_chan_test":
        results = []
        for label, cid in (("Private logs", LOGS_CHANNEL_ID or int(await get_setting("logs_channel_id", 0) or 0)),
                           ("Public feed", await _public_log_channel()),
                           ("Announcements", await _announcement_channel()),
                           ("Payment group", await _payment_group())):
            if not cid:
                results.append(f"• {label}: not set")
                continue
            try:
                await bot.send_message(cid, fancy(f"🧪 Test message — {label}"))
                results.append(f"• {label}: ✅ delivered")
            except Exception as e:
                results.append(f"• {label}: ❌ {str(e)[:60]}")
        await safe_callback_answer(event, "Test finished")
        await event.respond(fancy("🧪 **Channel test**\n\n" + "\n".join(results)),
                            buttons=[[color_btn("◀️ Back", "admin_channels", "default")]])
        return True
    elif data == "admin_force_join":
        t, b = await _force_join_screen()
        await _edit_quiet(event, t, b)
    elif data == "admin_fj_ap_add":
        user_states[user_id] = {"action": "fj_ap_add"}
        await event.edit(fancy("✅ **Approve user**\n\nSend the Telegram user ID. This user can use the bot without joining the force-join channels."),
                         buttons=[[color_btn("❌ Cancel", "admin_force_join", "default")]])
    elif data.startswith("admin_fj_ap_rm:"):
        ids = set(await _fj_exempt())
        ids.discard(int(data.split(":", 1)[1]))
        await _fj_exempt_save(ids)
        t, b = await _force_join_screen()
        await _edit_quiet(event, t, b)
    elif data == "admin_fj_add":
        user_states[user_id] = {"action": "fj_add"}
        await event.edit(fancy("➕ **Add force-join chat**\n\nSend `@username` or the numeric ID (like `-1001234567890`). "
                               "The bot must be an admin there."),
                         buttons=[[color_btn("❌ Cancel", "admin_force_join", "default")]])
    elif data.startswith("admin_fj_rm:"):
        stored = list(await _pay_set("force_join_channels", []) or [])
        try:
            stored.pop(int(data.split(":", 1)[1]))
            await _pay_put("force_join_channels", stored)
        except Exception:
            pass
        t, b = await _force_join_screen()
        await _edit_quiet(event, t, b)
    elif data == "admin_server3":
        t, b = await _server3_admin_screen()
        await _edit_quiet(event, t, b)
    elif data == "admin_server3_markup":
        user_states[user_id] = {"action": "s3_markup"}
        await event.edit(fancy(f"📈 **Server 3 markup**\n\nCurrent: `{await server3_server.get_markup_percent()}%`\n\nSend the new markup percent (0 – 500)."),
                         buttons=[[color_btn("❌ Cancel", "admin_server3", "default")]])
    elif data == "admin_server3_toggle":
        cur = await _server_active(SERVER3_NUMBER)
        active = await get_setting("server_active", None)
        active = dict(active) if isinstance(active, dict) else {}
        active[str(SERVER3_NUMBER)] = not cur
        await set_setting("server_active", active)
        t, b = await _server3_admin_screen()
        await _edit_quiet(event, t, b)
    await safe_callback_answer(event)
    return True

async def ext_admin_message(event, user_id: int, st: dict) -> bool:
    action = st.get("action")
    if action not in ("chan_edit", "fj_add", "fj_ap_add", "s3_markup"):
        return False
    if not await is_admin(user_id):
        user_states.pop(user_id, None)
        return True
    if action == "fj_ap_add":
        if not (event.message.text or "").strip().lstrip("-").isdigit():
            await event.respond(fancy("❌ Send a numeric Telegram user ID."))
            return True
        ids = set(await _fj_exempt())
        ids.add(int(event.message.text.strip()))
        await _fj_exempt_save(ids)
        user_states.pop(user_id, None)
        t, b = await _force_join_screen()
        await event.respond(t, buttons=b)
        return True
    text = (event.message.text or "").strip()
    if action == "chan_edit":
        try:
            cid = int(text)
        except ValueError:
            await event.respond(fancy("❌ Send a numeric chat ID, or `0` to disable."))
            return True
        if cid:
            try:
                await bot.send_message(cid, fancy("✅ Channel connected."))
            except Exception as e:
                await event.respond(fancy(f"❌ Could not post there: `{str(e)[:100]}`\n\nMake the bot an admin first."))
                return True
        await _pay_put(st["key"], cid)
        user_states.pop(user_id, None)
        t, b = await _channels_screen()
        await event.respond(t, buttons=b)
    elif action == "fj_add":
        parsed = _parse_chat_id(text)
        if parsed is None:
            await event.respond(fancy("❌ Send `@username` or a numeric ID."))
            return True
        try:
            ent = await bot.get_entity(parsed)
            await bot.get_permissions(ent, await bot.get_me())
        except Exception as e:
            await event.respond(fancy(f"❌ Could not access that chat: `{str(e)[:100]}`\n\nAdd the bot there first."))
            return True
        stored = list(await _pay_set("force_join_channels", []) or [])
        if text.lower() not in [str(x).lower() for x in stored]:
            stored.append(text)
            await _pay_put("force_join_channels", stored)
        user_states.pop(user_id, None)
        t, b = await _force_join_screen()
        await event.respond(t, buttons=b)
    else:
        try:
            val = float(text)
            assert 0 <= val <= 500
        except Exception:
            await event.respond(fancy("❌ Send a number between 0 and 500."))
            return True
        await server3_server.set_markup_percent(val)
        user_states.pop(user_id, None)
        t, b = await _server3_admin_screen()
        await event.respond(fancy(f"✅ Markup set to {val}%.\n\n") + t, buttons=b)
    return True

async def ext_startup():
    """One-time boot work for the ported features."""
    await reload_razorpay_keys()
    try:
        await deposits_col.create_index("payment_id", unique=True, sparse=True)
        await referral_signup_claims_col.create_index("referrer_id")
        await stock_deeplinks_col.create_index("token", unique=True)
        await bulk_orders_col.create_index([("user_id", 1), ("status", 1)])
    except Exception as e:
        log.warning(f"[ext] index creation: {e}")
    # Server 3 becomes the 3rd server automatically when its API key is configured.
    if server3_server.configured:
        try:
            if int(await get_setting("server_count", 2)) < SERVER3_NUMBER:
                await set_setting("server_count", SERVER3_NUMBER)
        except Exception as e:
            log.warning(f"[ext] server_count migration: {e}")


# ── 27.99 DISPATCHERS (called from callback_router / message_handler) ──
async def ext_callback(event, data: str, user_id: int, user) -> bool:
    """Runs before Vault's own router. Returns True when the callback was handled here."""
    if data.startswith("server3"):
        return await handle_server3_callback(event, data, user_id)
    for fn in (ext_accounts_callback, ext_upload_callback, ext_bulk_callback,
               ext_payments_callback, ext_payments_admin_callback, ext_admin_callback):
        if await fn(event, data, user_id):
            return True
    return await ext_referral_callback(event, data, user_id, user)

async def ext_message(event, user_id: int, state_data: dict) -> bool:
    """Runs before Vault's own message handler. Returns True when the message was handled here."""
    for fn in (ext_server3_message, ext_bulk_message, ext_accounts_message, ext_upload_message,
               ext_referral_message, ext_payments_admin_message, ext_admin_message,
               ext_payments_message):
        if await fn(event, user_id, state_data):
            return True
    return False


# <<EXT-END>>

# ─── 26. MAIN ────────────────────────────────────────────────────
async def stock_health_sweeper():
    """Round-robin live check of unsold stock. A session that was logged out is pulled from the bot
    within minutes (AccountManager marks it inactive -> never counted, listed or sold)."""
    await asyncio.sleep(60)
    sem = asyncio.Semaphore(4)

    async def _one(d):
        async with sem:
            try:
                await asyncio.wait_for(acc_mgr.validate_client(d["phone"]), 40)
            except Exception:
                pass
            with contextlib.suppress(Exception):
                await accounts_col.update_one({"_id": d["_id"], "status": "available"},
                                              {"$set": {"health_checked_at": datetime.utcnow()}})
    while True:
        try:
            docs = await (accounts_col.find({"status": "available", "phone": {"$exists": True}}, {"phone": 1})
                          .sort("health_checked_at", 1).limit(12).to_list(12))
            if docs:
                await asyncio.gather(*[_one(d) for d in docs])
        except Exception as e:
            log.warning(f"[stock_health_sweeper] {e}")
        await asyncio.sleep(15)

async def shutdown_http_sessions():
    """Close the pooled aiohttp sessions of both suppliers (safe to call twice)."""
    for srv in (vnh_server, server3_server):
        try:
            await srv.close()
        except Exception as e:
            log.warning(f"supplier session close failed: {e}")

async def main():
    threading.Thread(target=_start_health_server, daemon=True).start()
    await init_db()
    await bot.start(bot_token=BOT_TOKEN)

    global acc_mgr
    await ext_startup()
    if server3_server.configured:
        server3_server.start_warmer()      # stock lists are pre-fetched → Server 3 taps are instant
    acc_mgr = AccountManager(
        accounts_col, bot, API_ID, API_HASH, pending_otp_requests,
        admin_ids=await get_all_admin_ids(),
        otp_sent_notifier=notify_otp_sent_to_owner,
        btn=lambda text, data: color_btn(text, data, "default"),
        fmt=fancy,
        invalid_notifier=acc_invalid_notifier,
    )
    await acc_mgr.load_all()
    acc_mgr.start_supervisor()

    asyncio.create_task(_load_ui_flags())
    asyncio.create_task(_migrate_cat_prices())
    asyncio.create_task(stock_health_sweeper())
    asyncio.create_task(deposit_poller())
    if RENDER_EXTERNAL_URL:
        asyncio.create_task(self_ping())

    bot_name = await get_setting("bot_name", "Prime Vault")
    log.info(f"🚀 {bot_name} is running…")
    try:
        loop = asyncio.get_running_loop()
        for sig in (signal.SIGTERM, signal.SIGINT):          # docker stop / systemd / Ctrl+C
            loop.add_signal_handler(sig, lambda: asyncio.ensure_future(bot.disconnect()))
    except (NotImplementedError, RuntimeError):
        pass
    try:
        await bot.run_until_disconnected()
    finally:
        await shutdown_http_sessions()

if __name__ == "__main__":
    asyncio.run(main())
