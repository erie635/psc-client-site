# _PSC_TIMEOUT_PATCH applied
"""
PSC - Pulse Shopping Coin
Client-facing online shop with automatic PSC wallet creation + client registry.
+ Category grouping, login/register, account persistence.
+ Animated hero carousel.
+ In-memory caching for fast loads (10-min TTL).
+ Product sources: Jumia, Kilimall, Carrefour, Jiji, Fahavi, Text Book Centre,
  Naivas, Vivo, Copell, Masoko, Hotpoint, Samsung Brand Store.
+ Bonus PSC is used only as discount. Purchased PSC is used only as payment.
+ Daily bonus (1 PSC) is granted at 00:00 server time via background thread.
+ Purchase requests are forwarded to the admin's client_wallet_ledger.json.
+ Daily VISIT bonus: 1 PSC granted to the redeemable bucket on the first
  visit of the day (no login required), via _grant_daily_visit_bonus().
+ KYC submission + status (used by payout compliance gate).
+ THREE-BUCKET WALLET (Option C): wallet_psc (spendable), savings_psc (parked),
  deposit_psc (hold-only). Shop only reads wallet_psc.
+ Withdrawals: user requests are held and MUST be confirmed by the admin
  (manual payout, no automated transfers).
+ P2P PSC transfers between users.
+ Savings sub-balance with full UI manifest endpoint.
+ Deposit PSC pocket with move_in / move_out endpoints.
+ Blockchain mining endpoints + real-time WebSocket push.
+ AML/PEP/sanctions screening, CBK/KRA reporting, payout velocity checks.

PAYMENT GATEWAYS REMOVED:
- Flutterwave, Paystack, CoinGate, MoonPay integrations removed entirely.
- All /api/psc/topup/* endpoints removed.
- All /webhooks/* gateway callbacks removed.
- /api/wallet/deposit/initiate and /verify removed.
- Payment links (/pay/<token>) removed.
- Virtual Account issuance removed (relied on Flutterwave).
- Bank-list + account-resolution endpoints removed (relied on Flutterwave).
- Wallet funding is now ADMIN-MANUAL only (via /api/wallet/purchase with
  X-PSC-Admin-Token), P2P transfers, mining rewards, welcome bonus, and
  daily bonus/visit bonus. All other logic preserved.
"""

from dotenv import load_dotenv
load_dotenv()
from flask import Flask, jsonify, render_template, render_template_string, request, redirect, url_for, session
from flask_cors import CORS
import json
import hmac
import requests as _http
import os
import uuid
import random
import hashlib
from datetime import datetime, timedelta
from urllib.parse import quote_plus

import requests
from bs4 import BeautifulSoup

import time
import threading
from concurrent.futures import ThreadPoolExecutor, wait

from werkzeug.security import generate_password_hash, check_password_hash
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from filelock import FileLock

import warnings
warnings.filterwarnings("ignore", message="line buffering.*binary mode", category=RuntimeWarning)

# --- Portable path root (works on Windows / Linux / Docker) ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# --- Portable path root (works on Windows / Linux / Docker) ---

# --- Portable path root (works on Windows / Linux / Docker) ---


# === PSC PATCH: PLAYWRIGHT SEMAPHORE (A+B) ===
_PLAYWRIGHT_SEM = threading.Semaphore(1)

try:
    import playwright.sync_api as _psc_pw_sync
    _psc_orig_sync_playwright = _psc_pw_sync.sync_playwright

    class _PscSemPlaywright:
        def __init__(self, inner):
            self._inner = inner
            self._ctx_obj = None
        def __enter__(self):
            _PLAYWRIGHT_SEM.acquire()
            try:
                self._ctx_obj = self._inner.__enter__()
                return self._ctx_obj
            except BaseException:
                _PLAYWRIGHT_SEM.release()
                raise
        def __exit__(self, *exc):
            try:
                return self._inner.__exit__(*exc)
            finally:
                _PLAYWRIGHT_SEM.release()

    def _psc_sync_playwright(*a, **k):
        return _PscSemPlaywright(_psc_orig_sync_playwright(*a, **k))

    _psc_pw_sync.sync_playwright = _psc_sync_playwright
    print("[PSC PATCH] Playwright semaphore installed (max 1 concurrent).")
except Exception as _psc_pw_err:
    print("[PSC PATCH] Playwright semaphore not installed: " + str(_psc_pw_err))
# === END PSC PATCH: PLAYWRIGHT SEMAPHORE ===

# ---------- SIMPLE IN-MEMORY CACHE ----------
_PRODUCT_CACHE_DB = {}
_CACHE_LOCK = threading.Lock()

_PRODUCT_CACHE = {}
_CATEGORY_CACHE = {}


def _cache_get(key):
    with _CACHE_LOCK:
        entry = _PRODUCT_CACHE_DB.get(key)
        if not entry:
            return None
        ts, data = entry
        if time.time() - ts > CACHE_TTL_SECONDS:
            return None
        return data


def _cache_get_soft(key):
    with _CACHE_LOCK:
        entry = _PRODUCT_CACHE_DB.get(key)
        return entry[1] if entry else None


def _cache_set(key, value):
    with _CACHE_LOCK:
        _PRODUCT_CACHE_DB[key] = (time.time(), value)


def _cache_clear():
    with _CACHE_LOCK:
        _PRODUCT_CACHE_DB.clear()


# ============================================================
#  PSC â€” PERSISTENT DISK CACHE
# ============================================================

DISK_CACHE_FILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "psc_product_cache.json"
)
DISK_CACHE_LOCK = threading.Lock()
DISK_CACHE_SAVE_DEBOUNCE_SECONDS = 5.0
_DISK_CACHE_LAST_SAVE = 0.0
_DISK_CACHE_DIRTY = False
_DISK_CACHE_META = {}


def _load_disk_cache():
    if not os.path.exists(DISK_CACHE_FILE):
        return
    try:
        with open(DISK_CACHE_FILE, "r", encoding="utf-8") as f:
            payload = json.load(f)
        entries = payload.get("entries") or {}
        meta = payload.get("meta") or {}
        now = time.time()
        with _CACHE_LOCK:
            for key, val in entries.items():
                if not isinstance(val, dict):
                    continue
                data = val.get("data")
                ts = float(val.get("ts") or now)
                if data is None:
                    continue
                _PRODUCT_CACHE_DB[key] = (ts, data)
        _DISK_CACHE_META.update(meta)
        print(f"[PSC CACHE] Loaded {len(entries)} disk cache entries.")
    except Exception as e:
        print(f"[PSC CACHE] disk cache load failed: {e}")


def _save_disk_cache(force=False):
    global _DISK_CACHE_LAST_SAVE, _DISK_CACHE_DIRTY
    now = time.time()
    if not force and (now - _DISK_CACHE_LAST_SAVE) < DISK_CACHE_SAVE_DEBOUNCE_SECONDS:
        _DISK_CACHE_DIRTY = True
        return
    if not DISK_CACHE_LOCK.acquire(blocking=False):
        _DISK_CACHE_DIRTY = True
        return
    try:
        with _CACHE_LOCK:
            entries = {
                k: {"ts": v[0], "data": v[1]}
                for k, v in _PRODUCT_CACHE_DB.items()
            }
        payload = {
            "saved_at": now,
            "entries": entries,
            "meta": _DISK_CACHE_META,
        }
        tmp = DISK_CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False)
        os.replace(tmp, DISK_CACHE_FILE)
        _DISK_CACHE_LAST_SAVE = now
        _DISK_CACHE_DIRTY = False
    except Exception as e:
        print(f"[PSC CACHE] disk cache save failed: {e}")
    finally:
        DISK_CACHE_LOCK.release()


def _cache_save_async():
    threading.Thread(target=_save_disk_cache, daemon=True).start()


# ---------- GLOBAL SCRAPE LOCK + PER-QUERY COOLDOWN ----------
_SCRAPE_LOCK = threading.Lock()

_SCRAPE_COOLDOWN_SECONDS = 10
_LAST_SCRAPE_AT = {}
_LAST_SCRAPE_AT_LOCK = threading.Lock()

_CATEGORY_IMAGE_CACHE = {}
_CATEGORY_IMAGE_LOCK = threading.Lock()
_CATEGORY_IMAGE_TTL = 300

_JUMIA_BLOCKED_UNTIL = 0.0
_JUMIA_BLOCKED_LOCK = threading.Lock()
_JUMIA_BACKOFF_SECONDS = 300

_KILIMALL_BLOCKED_UNTIL = 0.0
_KILIMALL_BLOCKED_LOCK = threading.Lock()
_KILIMALL_BACKOFF_SECONDS = 300

_CARREFOUR_BLOCKED_UNTIL = 0.0
_CARREFOUR_BLOCKED_LOCK = threading.Lock()
_CARREFOUR_BACKOFF_SECONDS = 300

_JIJI_BLOCKED_UNTIL = 0.0
_JIJI_BLOCKED_LOCK = threading.Lock()
_JIJI_BACKOFF_SECONDS = 300

_VENDOR_SCRAPE_TIMEOUT_SECONDS = 90
_VENDOR_EXECUTOR_MAX_WORKERS = 4

_USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/141.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/141.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_5 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:126.0) Gecko/20100101 Firefox/126.0",
    "Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:125.0) Gecko/20100101 Firefox/125.0",
]


def _random_ua():
    return random.choice(_USER_AGENTS)


def _jitter(base_ms, spread_ms=2000):
    return random.randint(int(base_ms), int(base_ms) + int(spread_ms))


PSC_PROXY_SERVER   = os.getenv("PSC_PROXY_SERVER", "").strip()
PSC_PROXY_USERNAME = os.getenv("PSC_PROXY_USERNAME", "").strip()
PSC_PROXY_PASSWORD = os.getenv("PSC_PROXY_PASSWORD", "").strip()
_PSC_PROXY_DEAD_UNTIL = 0.0

PSC_PROXY_SERVERS  = [
    s.strip() for s in os.getenv("PSC_PROXY_SERVERS", "").split(",") if s.strip()
]



def _requests_proxy_config():
    global _PSC_PROXY_DEAD_UNTIL
    if time.time() < _PSC_PROXY_DEAD_UNTIL:
        return None
    server = ""
    if PSC_PROXY_SERVERS:
        server = random.choice(PSC_PROXY_SERVERS)
    elif PSC_PROXY_SERVER:
        server = PSC_PROXY_SERVER
    if not server:
        return None
    if PSC_PROXY_USERNAME and PSC_PROXY_PASSWORD:
        from urllib.parse import urlparse, urlunparse
        parsed = urlparse(server)
        if parsed.hostname:
            netloc = f"{PSC_PROXY_USERNAME}:{PSC_PROXY_PASSWORD}@{parsed.hostname}"
            if parsed.port:
                netloc += f":{parsed.port}"
            server = urlunparse((parsed.scheme, netloc, parsed.path, parsed.params, parsed.query, parsed.fragment))
    return {"http": server, "https": server}

def _playwright_proxy_config():
    global _PSC_PROXY_DEAD_UNTIL
    if time.time() < _PSC_PROXY_DEAD_UNTIL:
        return None
    server = ""
    if PSC_PROXY_SERVERS:
        server = random.choice(PSC_PROXY_SERVERS)
    elif PSC_PROXY_SERVER:
        server = PSC_PROXY_SERVER

    if not server:
        return None

    cfg = {"server": server}
    if PSC_PROXY_USERNAME:
        cfg["username"] = PSC_PROXY_USERNAME
    if PSC_PROXY_PASSWORD:
        cfg["password"] = PSC_PROXY_PASSWORD
    return cfg


_STEALTH_INIT_JS = r"""
Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
Object.defineProperty(navigator, 'languages', { get: () => ['en-KE','en-US','en'] });
try {
    Object.defineProperty(navigator, 'plugins', { get: () => [
        {name: 'PDF Viewer'}, {name: 'Chrome PDF Viewer'}, {name: 'Native Client'}
    ]});
} catch (e) {}
window.chrome = window.chrome || { runtime: {}, app: {}, csi: function(){}, loadTimes: function(){} };
try {
    const _origQuery = window.navigator.permissions.query;
    window.navigator.permissions.query = (p) => (
        p && p.name === 'notifications'
            ? Promise.resolve({ state: Notification.permission })
            : _origQuery(p)
    );
} catch (e) {}
try {
    const gp = WebGLRenderingContext.prototype.getParameter;
    WebGLRenderingContext.prototype.getParameter = function(p) {
        if (p === 37445) return 'Intel Inc.';
        if (p === 37446) return 'Intel Iris OpenGL Engine';
        return gp.call(this, p);
    };
} catch (e) {}
"""


def _new_stealth_page(browser, locale="en-KE", tz="Africa/Nairobi"):
    ctx = browser.new_context(
        user_agent=_random_ua(),
        viewport={"width": 1920, "height": 1080},
        locale=locale,
        timezone_id=tz,
        screen={"width": 1920, "height": 1080},
        device_scale_factor=1,
        is_mobile=False,
        has_touch=False,
        java_script_enabled=True,
        extra_http_headers={"Accept-Language": "en-KE,en-US;q=0.9,en;q=0.8"},
    )
    ctx.add_init_script(_STEALTH_INIT_JS)
    page = ctx.new_page()
    return ctx, page


def _cloudflare_present(page):
    try:
        title = (page.title() or "").lower()
        body = ""
        try:
            body = (page.content() or "").lower()[:6000]
        except Exception:
            pass
        marks = (
            "just a moment", "attention required", "checking your browser",
            "cloudflare", "verify you are human",
            "enable javascript and cookies",
        )
        return any(m in title or m in body for m in marks)
    except Exception:
        return False


def _wait_for_cloudflare_clear(page, max_seconds=25):
    import time as _t
    deadline = _t.time() + max_seconds
    while _t.time() < deadline:
        if not _cloudflare_present(page):
            return True
        try:
            page.wait_for_timeout(1200)
        except Exception:
            _t.sleep(1)
    return not _cloudflare_present(page)


def _launch_browser(p):
    global _PSC_PROXY_DEAD_UNTIL
    kwargs = {
        "headless": True,
        "args": [
            "--disable-blink-features=AutomationControlled",
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "--disable-gpu",
            "--single-process",
            "--no-zygote",
            "--disable-accelerated-2d-canvas",
            "--disable-setuid-sandbox",
            "--js-flags=--max-old-space-size=128",
            "--window-size=1920,1080",
            "--start-maximized",
            "--disable-features=IsolateOrigins,site-per-process",
            "--disable-site-isolation-trials",
            "--disable-background-timer-throttling",
            "--disable-backgrounding-occluded-windows",
            "--disable-renderer-backgrounding",
            "--no-first-run",
            "--no-default-browser-check",
            "--lang=en-KE,en-US,en",
        ],
    }
    proxy_cfg = _playwright_proxy_config()
    if proxy_cfg:
        kwargs["proxy"] = proxy_cfg
    try:
        return p.chromium.launch(**kwargs)
    except Exception as e:
        if "proxy" in kwargs and ("ERR_TUNNEL_CONNECTION_FAILED" in str(e) or "402" in str(e) or "Proxy" in str(e)):
            print("[PSC] Playwright proxy failed. Retrying WITHOUT proxy for 1 hour...")
            _PSC_PROXY_DEAD_UNTIL = time.time() + 3600
            kwargs.pop("proxy", None)
            return p.chromium.launch(**kwargs)
        raise


def _scrape_recently_done(query_key):
    with _LAST_SCRAPE_AT_LOCK:
        ts = _LAST_SCRAPE_AT.get(query_key)
    if ts is None:
        return False
    return (time.time() - ts) < _SCRAPE_COOLDOWN_SECONDS


def _mark_scrape_done(query_key):
    with _LAST_SCRAPE_AT_LOCK:
        _LAST_SCRAPE_AT[query_key] = time.time()


VENDORS = {
    "jumia": {"key": "jumia", "label": "Jumia", "prefix": "jumia:",
              "url_template": "https://www.jumia.co.ke/catalog/?q={query}"},
    "kilimall": {"key": "kilimall", "label": "Kilimall", "prefix": "kilimall:",
                 "url_template": "https://www.kilimall.co.ke/search?q={query}"},
    "carrefour": {"key": "carrefour", "label": "Carrefour", "prefix": "carrefour:",
                  "url_template": "https://www.carrefour.ke/mafken/en/search?keyword={query}"},
    "jiji": {"key": "jiji", "label": "Jiji", "prefix": "jiji:",
             "url_template": "https://jiji.co.ke/search?query={query}"},
    "fahavi": {"key": "fahavi", "label": "Fahavi Computers", "prefix": "fahavi:",
               "url_template": "https://fahavicomputers.co.ke/?s={query}&post_type=product"},
    "textbookcentre": {"key": "textbookcentre", "label": "Text Book Centre", "prefix": "tbc:",
                       "url_template": "https://textbookcentre.com/catalogsearch/result/?q={query}"},
    "naivas": {"key": "naivas", "label": "Naivas", "prefix": "naivas:",
               "url_template": "https://naivas.co.ke/search?q={query}"},
    "vivo": {"key": "vivo", "label": "Vivo", "prefix": "vivo:",
             "url_template": "https://vivo.co.ke/catalogsearch/result/?q={query}"},
    "copell": {"key": "copell", "label": "Copell", "prefix": "copell:",
               "url_template": "https://copell.co.ke/?s={query}&post_type=product"},
    "masoko": {"key": "masoko", "label": "Safaricom Masoko", "prefix": "masoko:",
               "url_template": "https://masoko.co.ke/search?q={query}"},
    "hotpoint": {"key": "hotpoint", "label": "Hotpoint Appliances", "prefix": "hotpoint:",
                 "url_template": "https://hotpoint.co.ke/catalogsearch/result/?q={query}"},
    "samsungstore": {"key": "samsungstore", "label": "Samsung Brand Store", "prefix": "samsung:",
                     "url_template": "https://samsungbrandstore.co.ke/catalogsearch/result/?q={query}"},
}

_VENDOR_BY_LABEL = {v["label"].lower(): v for v in VENDORS.values()}


def _vendor_url(vendor_key, query):
    v = VENDORS.get(str(vendor_key or "").strip().lower())
    if not v:
        return ""
    try:
        return v["url_template"].format(query=quote_plus(str(query or "").strip()))
    except Exception:
        return ""


def _extract_vendor_hint(query):
    raw = str(query or "").strip()
    low = raw.lower()
    for v in VENDORS.values():
        p = v["prefix"]
        if low.startswith(p):
            return v["key"], raw[len(p):].strip()
    return None, raw


def _vendor_for_source(source_name):
    return _VENDOR_BY_LABEL.get(str(source_name or "").strip().lower(), {}).get("key", "")


_VENDOR_FIELDS_TO_STRIP = ("vendor", "vendor_url", "source")


def _strip_vendor_fields(product):
    if not isinstance(product, dict):
        return product
    clean = {}
    for k, v in product.items():
        if k in _VENDOR_FIELDS_TO_STRIP:
            continue
        clean[k] = v
    return clean


def _strip_products_for_client(products):
    return [_strip_vendor_fields(p) for p in (products or [])]


def _sanitize_client_query(raw):
    if not raw:
        return raw
    _hint, cleaned = _extract_vendor_hint(raw)
    return cleaned


_FILLER_WORDS = {
    "smart", "phone", "phones", "mobile", "cell", "cellphone",
    "buy", "shop", "online", "cheap", "best", "good", "new",
    "used", "second", "hand", "for", "sale", "in", "kenya",
    "the", "a", "an", "and", "or", "with", "without",
    "offer", "offers", "deal", "deals", "price", "prices",
}


def _normalize_search_query(raw):
    cleaned = _sanitize_client_query(raw)
    if not cleaned:
        return cleaned
    words = cleaned.split()
    if len(words) <= 2:
        return cleaned
    kept = [w for w in words if w.lower() not in _FILLER_WORDS]
    if not kept:
        return cleaned
    return " ".join(kept)


# ---------- CONFIG ----------
PSC_TO_KES_RATE = 100
WELCOME_BONUS = 6000
DAILY_LOGIN_BONUS_KES = 100
DAILY_LOGIN_BONUS_PSC = round(DAILY_LOGIN_BONUS_KES / PSC_TO_KES_RATE, 2)
BONUS_DISCOUNT_RATE = 0.01
MIN_BALANCE_TO_SHOP = 5.0
CACHE_TTL_SECONDS = 600
ADMIN_PHONE = "0796208133"

WALLET_DIR = os.path.join(BASE_DIR, "wallets")
ORDERS_FILE = os.path.join(BASE_DIR, "orders_from_clients.json")
CLIENTS_FILE = os.path.join(BASE_DIR, "client_registry.json")

ADMIN_CLIENT_WALLETS_FILE = os.path.join(BASE_DIR, "client_wallets.json")
ADMIN_LEDGER_FILE = os.path.join(BASE_DIR, "client_wallet_ledger.json")

PAYMENTS_FILE         = os.path.join(BASE_DIR, "payments.json")
WITHDRAWAL_QUEUE_FILE = os.path.join(BASE_DIR, "withdrawal_queue.json")
PAYOUT_AUDIT_FILE     = os.path.join(BASE_DIR, "payout_audit.json")

MARKUP_DEFAULT = 0.05

CATEGORY_MARKUPS = {
    "laptop": 0.15, "laptops": 0.15, "notebook": 0.15, "notebooks": 0.15,
    "macbook": 0.15, "macbooks": 0.15, "chromebook": 0.15,
    "ultrabook": 0.15, "desktop": 0.15, "workstation": 0.15,
    "pc": 0.15, "computer": 0.15, "computers": 0.15,
    "hp": 0.15, "dell": 0.15, "lenovo": 0.15, "asus": 0.15,
    "acer": 0.15, "toshiba": 0.15, "msi": 0.15, "razer": 0.15,
    "inspiron": 0.15, "pavilion": 0.15, "thinkpad": 0.15,
    "ideapad": 0.15, "zenbook": 0.15, "vivobook": 0.15,
    "spectre": 0.15, "envy": 0.15, "omen": 0.15, "predator": 0.15,

    "phone": 0.15, "phones": 0.15, "smartphone": 0.15, "smartphones": 0.15,
    "iphone": 0.15, "iphones": 0.15,
    "galaxy": 0.15, "redmi": 0.15, "poco": 0.15,
    "tecno": 0.15, "infinix": 0.15, "oppo": 0.15, "vivo": 0.15,
    "oneplus": 0.15, "huawei": 0.15, "xiaomi": 0.15,
    "nokia": 0.15, "itel": 0.15, "realme": 0.15,
    "tablet": 0.15, "tablets": 0.15, "ipad": 0.15, "ipads": 0.15,
    "tab": 0.15, "mobile": 0.15, "cellphone": 0.15,

    "jewelry": 0.15, "jewellery": 0.15, "jewel": 0.15, "jewels": 0.15,
    "watch": 0.15, "watches": 0.15, "wristwatch": 0.15, "smartwatch": 0.15,
    "ring": 0.15, "rings": 0.15,
    "necklace": 0.15, "necklaces": 0.15,
    "earring": 0.15, "earrings": 0.15,
    "bracelet": 0.15, "bracelets": 0.15,
    "pendant": 0.15, "pendants": 0.15,
    "chain": 0.15, "chains": 0.15,
    "gold": 0.15, "silver": 0.15,
    "diamond": 0.15, "diamonds": 0.15,
    "gemstone": 0.15, "gemstones": 0.15,

    "fridge": 0.15, "fridges": 0.15,
    "refrigerator": 0.15, "refrigerators": 0.15,
    "freezer": 0.15, "freezers": 0.15,
    "deep freezer": 0.15, "deepfreezer": 0.15, "deep-freezer": 0.15,
    "fridge freezer": 0.15, "fridge-freezer": 0.15,
    "cooler": 0.15, "coolers": 0.15,
    "cold room": 0.15, "coldroom": 0.15,

    "beauty": 0.15, "beauty products": 0.15,
    "health & beauty": 0.15, "health and beauty": 0.15,
    "cosmetic": 0.15, "cosmetics": 0.15,
    "makeup": 0.15, "make-up": 0.15, "make up": 0.15,
    "skincare": 0.15, "skin care": 0.15,
    "perfume": 0.15, "perfumes": 0.15,
    "fragrance": 0.15, "fragrances": 0.15,
    "lipstick": 0.15, "lipsticks": 0.15,
    "lip gloss": 0.15, "lipgloss": 0.15,
    "lip balm": 0.15, "lipbalm": 0.15,
    "mascara": 0.15, "eyeliner": 0.15, "eyeshadow": 0.15,
    "eyebrow": 0.15, "eyebrows": 0.15,
    "blush": 0.15, "blusher": 0.15,
    "concealer": 0.15,
    "nail polish": 0.15, "nailpolish": 0.15,
    "body lotion": 0.15, "body cream": 0.15,
    "lotion": 0.15, "lotions": 0.15,
    "face cream": 0.15, "facecream": 0.15,
    "face wash": 0.15, "facewash": 0.15,
    "moisturizer": 0.15, "moisturiser": 0.15,
    "moisturizing": 0.15, "moisturising": 0.15,
    "shampoo": 0.15, "shampoos": 0.15,
    "conditioner": 0.15, "conditioners": 0.15,
    "deodorant": 0.15, "deodorants": 0.15,
    "serum": 0.15, "serums": 0.15,
    "cleanser": 0.15, "cleansers": 0.15,
    "hair care": 0.15, "haircare": 0.15,
    "wig": 0.15, "wigs": 0.15,
    "hair extension": 0.15, "hair extensions": 0.15,
}


app = Flask(__name__)

try:
    import auto_share
    auto_share.install(app, port=5001, auto_start=True)
except Exception as _as_e:
    print(f"[AUTO-SHARE] skipped: {_as_e}")

from flask_session import Session
app.config["SESSION_TYPE"] = "filesystem"
app.config["SESSION_FILE_DIR"] = os.path.join(BASE_DIR, "flask_sessions")
app.config["SESSION_PERMANENT"] = True
app.config["SESSION_USE_SIGNER"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["SESSION_COOKIE_SECURE"] = False
Session(app)

app.secret_key = os.environ.get(
    "PSC_SECRET_KEY",
    "psc_secret_key_2026_pulse_shopping_coin"
)

app.permanent_session_lifetime = timedelta(hours=12)

CORS(app, origins=[
    "http://127.0.0.1:5001",
    "http://localhost:5001",
])

limiter = Limiter(
    key_func=get_remote_address,
    app=app,
    default_limits=[],
    storage_uri="memory://",
)


_CLIENTS_SIG_FILE = CLIENTS_FILE + ".sig"
_CLIENTS_HMAC_SECRET = os.environ.get(
    "PSC_REGISTRY_SECRET",
    "psc_registry_hmac_secret_change_me"
)


def _sign_clients_bytes(body_bytes):
    return hmac.new(
        _CLIENTS_HMAC_SECRET.encode("utf-8"),
        body_bytes,
        hashlib.sha256,
    ).hexdigest()


def _verify_clients_signature(body_bytes):
    if not os.path.exists(_CLIENTS_SIG_FILE):
        return False
    try:
        with open(_CLIENTS_SIG_FILE, "r", encoding="utf-8") as f:
            stored = f.read().strip()
        return hmac.compare_digest(stored, _sign_clients_bytes(body_bytes))
    except Exception:
        return False


_CLIENTS_LOCK = FileLock(CLIENTS_FILE + ".lock")

_LOGIN_AUDIT_FILE = os.path.join(
    os.path.dirname(CLIENTS_FILE) or ".",
    "login_audit.log"
)


def _audit_login(phone, success, reason=""):
    try:
        line = (
            f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} | "
            f"phone={_normalize_phone(phone)} | "
            f"success={bool(success)} | "
            f"reason={reason or ''}\n"
        )
        with open(_LOGIN_AUDIT_FILE, "a", encoding="utf-8") as f:
            f.write(line)
    except Exception:
        pass


def _ensure_wallet_dir():
    if not os.path.exists(WALLET_DIR):
        os.makedirs(WALLET_DIR)


def _load_wallets():
    _ensure_wallet_dir()
    wallets = {}
    for fname in os.listdir(WALLET_DIR):
        if fname.endswith(".json"):
            try:
                with open(os.path.join(WALLET_DIR, fname), "r", encoding="utf-8") as f:
                    data = json.load(f)
                    if "address" in data:
                        wallets[data["address"]] = data
            except Exception:
                pass
    return wallets


def _save_wallet(wallet):
    _ensure_wallet_dir()
    path = os.path.join(WALLET_DIR, wallet["address"] + ".json")

    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as _f:
                _existing = json.load(_f)
            _existing_addr = str(_existing.get("address", "")).strip()
            _new_addr = str(wallet.get("address", "")).strip()
            if _existing_addr and _existing_addr != _new_addr:
                raise PermissionError(
                    f"Refusing to overwrite wallet {_existing_addr} "
                    f"with {_new_addr}"
                )
        except PermissionError:
            raise
        except Exception:
            pass

    with open(path, "w", encoding="utf-8") as f:
        json.dump(wallet, f, indent=2)


def _load_orders():
    if not os.path.exists(ORDERS_FILE):
        return []
    try:
        with open(ORDERS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []


def _save_orders(orders):
    with open(ORDERS_FILE, "w", encoding="utf-8") as f:
        json.dump(orders, f, indent=2, ensure_ascii=False)


def _next_order_id(orders):
    return f"CLI-{len(orders) + 1:05d}"


def _stable_product_id(name, source="", category="", kes_price=None):
    identity = "|".join([
        str(source or "").strip().lower(),
        str(category or "").strip().lower(),
        str(name or "").strip().lower(),
    ])
    digest = hashlib.sha256(identity.encode("utf-8")).hexdigest()
    return 100000 + (int(digest[:12], 16) % 8_000_000_000_000)


def _register_products(products):
    for product in products:
        if not product:
            continue
        product["id"] = _stable_product_id(
            product.get("name", ""),
            product.get("source", ""),
            product.get("category", ""),
            product.get("kes_price")
        )
        if "save_more" not in product:
            product["save_more"] = (
                str(product.get("source", "")).strip().lower() == "carrefour"
            )
        src = product.get("source", "")
        vkey = _vendor_for_source(src)
        product["vendor"] = vkey
        if vkey and not product.get("vendor_url"):
            product["vendor_url"] = _vendor_url(vkey, product.get("name", ""))
        _PRODUCT_CACHE[product["id"]] = product
    return products


def _admin_merge_wallet(address, name="", phone="", email="",
                       mpesa_number="", purchased_psc=None, bonus_psc=None,
                       savings_psc=None, deposit_psc=None):
    if not address:
        return
    try:
        if os.path.exists(ADMIN_CLIENT_WALLETS_FILE):
            with open(ADMIN_CLIENT_WALLETS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                data = {}
        else:
            data = {}
    except Exception:
        data = {}

    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    existing = data.get(address, {}) or {}

    if name: existing["name"] = name
    if phone: existing["phone"] = phone
    if email: existing["email"] = email
    if mpesa_number: existing["mpesa_number"] = mpesa_number
    existing.setdefault("wallet_address", address)

    if purchased_psc is None:
        existing.setdefault("purchased_psc", 0.0)
    else:
        existing["purchased_psc"] = float(purchased_psc)

    if bonus_psc is None:
        existing.setdefault("bonus_psc", 0.0)
    else:
        existing["bonus_psc"] = float(bonus_psc)

    if savings_psc is None:
        existing.setdefault("savings_psc", 0.0)
    else:
        existing["savings_psc"] = float(savings_psc)

    if deposit_psc is None:
        existing.setdefault("deposit_psc", 0.0)
    else:
        existing["deposit_psc"] = float(deposit_psc)

    existing.setdefault("created_at", now)
    existing["updated_at"] = now
    data[address] = existing

    tmp = ADMIN_CLIENT_WALLETS_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        os.replace(tmp, ADMIN_CLIENT_WALLETS_FILE)
    except Exception as e:
        print(f"[ADMIN-SYNC] wallet merge failed: {e}")


def _admin_ledger_add(entry):
    try:
        if os.path.exists(ADMIN_LEDGER_FILE):
            with open(ADMIN_LEDGER_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, list):
                data = []
        else:
            data = []
    except Exception:
        data = []

    data.append(entry)
    tmp = ADMIN_LEDGER_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        os.replace(tmp, ADMIN_LEDGER_FILE)
    except Exception as e:
        print(f"[ADMIN-SYNC] ledger write failed: {e}")


def _load_clients():
    if not os.path.exists(CLIENTS_FILE):
        return {}
    try:
        with open(CLIENTS_FILE, "rb") as _bf:
            _raw_body = _bf.read()

        if not _verify_clients_signature(_raw_body):
            print(
                "[SECURITY] client_registry.json signature mismatch or "
                "missing."
            )

        clients = json.loads(_raw_body.decode("utf-8"))
        if not isinstance(clients, dict):
            return {}

        migrated = False
        for _key, _cli in clients.items():
            if not isinstance(_cli, dict):
                continue
            pwd = _cli.get("password")
            if not pwd:
                continue
            if ":" not in str(pwd) or len(str(pwd)) < 30:
                _cli["password"] = generate_password_hash(str(pwd))
                migrated = True

        if migrated:
            try:
                _save_clients(clients, resign_only=True)
                print("[SECURITY] Migrated plaintext passwords to hashes.")
            except Exception as e:
                print(f"[SECURITY] Password migration save failed: {e}")

        return clients
    except Exception:
        return {}


def _save_clients(clients, resign_only=False):
    with _CLIENTS_LOCK:
        with open(CLIENTS_FILE, "w", encoding="utf-8") as f:
            json.dump(clients, f, indent=2, ensure_ascii=False)
        try:
            with open(CLIENTS_FILE, "rb") as bf:
                body = bf.read()
            with open(_CLIENTS_SIG_FILE, "w", encoding="utf-8") as sf:
                sf.write(_sign_clients_bytes(body))
        except Exception as e:
            print(f"[SECURITY] signature write failed: {e}")


def _normalize_phone(phone):
    if not phone:
        return ""
    return "".join(ch for ch in str(phone) if ch.isdigit())


def _normalize_email(email):
    if not email:
        return ""
    return str(email).strip().lower()


def _email_in_use(email, except_key=None):
    normalized = _normalize_email(email)
    if not normalized:
        return False
    clients = _load_clients()
    for key, client in clients.items():
        if key == except_key:
            continue
        if _normalize_email(client.get("email", "")) == normalized:
            return True
    return False


def _phone_belongs_to_wallet(phone, wallet_address):
    if not phone or not wallet_address:
        return False
    client = get_client_by_phone(phone)
    if not client:
        return False
    return str(client.get("wallet_address", "")).strip() == str(wallet_address).strip()


def _email_belongs_to_phone(email, phone):
    normalized = _normalize_email(email)
    if not normalized:
        return True
    key = _normalize_phone(phone)
    clients = _load_clients()
    for existing_key, client in clients.items():
        if _normalize_email(client.get("email", "")) == normalized:
            if existing_key != key:
                return False
    return True


def get_client_by_phone(phone):
    clients = _load_clients()
    return clients.get(_normalize_phone(phone))


def upsert_client(phone, shipping, wallet_address):
    if not phone:
        return
    key = _normalize_phone(phone)
    clients = _load_clients()
    existing = clients.get(key, {})
    existing.update({
        "phone": phone,
        "name": shipping.get("name", existing.get("name", "")),
        "email": shipping.get("email", existing.get("email", "")),
        "address": shipping.get("address", existing.get("address", "")),
        "city": shipping.get("city", existing.get("city", "")),
        "landmark": shipping.get("landmark", existing.get("landmark", "")),
        "wallet_address": wallet_address or existing.get("wallet_address", ""),
        "last_order_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "first_seen_at": existing.get(
            "first_seen_at",
            datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        ),
    })
    clients[key] = existing
    _save_clients(clients)

    _admin_merge_wallet(
        address=existing.get("wallet_address", ""),
        name=existing.get("name", ""),
        phone=existing.get("phone", phone),
        email=existing.get("email", ""),
        mpesa_number=existing.get("mpesa_number", ""),
    )


def _wallet_total(wallet):
    return round(
        float(wallet.get("wallet_psc", 0) or 0)
        + float(wallet.get("bonus_psc", 0) or 0)
        + float(wallet.get("savings_psc", 0) or 0)
        + float(wallet.get("deposit_psc", 0) or 0),
        2
    )


def _ensure_wallet_structure(wallet):
    if "wallet_psc" not in wallet or "bonus_psc" not in wallet:
        legacy_balance = float(wallet.get("balance", 0) or 0)
        wallet.setdefault("wallet_psc", legacy_balance)
        wallet.setdefault("bonus_psc", 0.0)

    wallet["wallet_psc"] = round(float(wallet.get("wallet_psc", 0) or 0), 2)
    wallet["bonus_psc"] = round(float(wallet.get("bonus_psc", 0) or 0), 2)
    wallet["savings_psc"] = round(float(wallet.get("savings_psc", 0) or 0), 2)
    wallet["deposit_psc"] = round(float(wallet.get("deposit_psc", 0) or 0), 2)
    wallet["balance"] = _wallet_total(wallet)

    wallet.setdefault("bonus_given", round(float(wallet.get("bonus_psc", 0) or 0), 2))
    wallet.setdefault("daily_login_bonus_psc", 0.0)
    wallet.setdefault("last_login_bonus_date", None)
    wallet.setdefault("purchase_history", [])
    return wallet


def create_client_wallet():
    address = "PSC" + uuid.uuid4().hex[:32]
    private_key = uuid.uuid4().hex + uuid.uuid4().hex

    wallet = {
        "address": address,
        "private_key": private_key,
        "wallet_psc": 0.0,
        "bonus_psc": float(WELCOME_BONUS),
        "savings_psc": 0.0,
        "deposit_psc": 0.0,
        "balance": float(WELCOME_BONUS),
        "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "bonus_given": float(WELCOME_BONUS),
        "daily_login_bonus_psc": 0.0,
        "last_login_bonus_date": None,
        "purchase_history": [],
        "orders": [],
    }
    _save_wallet(wallet)
    return wallet


def get_wallet(address):
    if not address:
        return None
    path = os.path.join(WALLET_DIR, address + ".json")
    if not os.path.exists(path):
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            wallet = json.load(f)
        wallet = _ensure_wallet_structure(wallet)
        _save_wallet(wallet)
        return wallet
    except Exception:
        return None


def _add_purchased_psc(address, amount_psc, kes_amount=None, payment_reference=""):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found", None

    amount_psc = round(float(amount_psc), 2)
    if amount_psc <= 0:
        return False, "PSC purchase amount must be greater than zero.", wallet

    wallet["wallet_psc"] = round(float(wallet.get("wallet_psc", 0)) + amount_psc, 2)
    wallet["balance"] = _wallet_total(wallet)
    wallet.setdefault("purchase_history", [])
    wallet["purchase_history"].append({
        "psc": amount_psc,
        "kes": round(float(kes_amount), 2) if kes_amount is not None else round(amount_psc * PSC_TO_KES_RATE, 2),
        "payment_reference": payment_reference or "",
        "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    })
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True, "OK", wallet


def _normalize_credit_target(target):
    t = str(target or "").strip().lower()
    if t in ("wallet", "spendable", "wallet_psc", ""):
        return "spendable"
    if t in ("savings", "savings_psc"):
        return "savings"
    if t in ("deposit", "deposit_psc"):
        return "deposit"
    return "spendable"


def _add_psc_to_target(address, amount_psc, target="spendable",
                       kes_amount=None, payment_reference="",
                       audit_type="TOPUP"):
    target = _normalize_credit_target(target)
    if target == "spendable":
        return _add_purchased_psc(
            address, amount_psc,
            kes_amount=kes_amount,
            payment_reference=payment_reference,
        )

    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found", None

    amount_psc = round(float(amount_psc), 2)
    if amount_psc <= 0:
        return False, "PSC credit amount must be greater than zero.", wallet

    if target == "savings":
        wallet["savings_psc"] = round(float(wallet.get("savings_psc", 0) or 0) + amount_psc, 2)
    else:
        wallet["deposit_psc"] = round(float(wallet.get("deposit_psc", 0) or 0) + amount_psc, 2)

    wallet["balance"] = _wallet_total(wallet)
    wallet.setdefault("purchase_history", [])
    wallet["purchase_history"].append({
        "psc": amount_psc,
        "kes": round(float(kes_amount), 2) if kes_amount is not None else round(amount_psc * PSC_TO_KES_RATE, 2),
        "payment_reference": payment_reference or "",
        "target": target,
        "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    })
    _save_wallet(wallet)

    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )

    try:
        _admin_ledger_add({
            "type": audit_type,
            "target": target,
            "wallet_address": address,
            "amount_psc": amount_psc,
            "amount_kes": round(float(kes_amount), 2) if kes_amount is not None
                          else round(amount_psc * PSC_TO_KES_RATE, 2),
            "payment_reference": payment_reference or "",
            "status": "COMPLETED",
            "time": _now(),
        })
    except Exception as e:
        print(f"[TARGET-CREDIT] ledger write failed: {e}")

    return True, "OK", wallet


def add_daily_login_bonus(address):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found", None

    today = datetime.now().strftime("%Y-%m-%d")
    if wallet.get("last_login_bonus_date") == today:
        return True, "Daily login bonus already awarded today.", wallet

    wallet["daily_login_bonus_psc"] = round(
        float(wallet.get("daily_login_bonus_psc", 0) or 0) + DAILY_LOGIN_BONUS_PSC, 2
    )
    wallet["last_login_bonus_date"] = today
    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)

    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return (
        True,
        f"Daily login bonus: {DAILY_LOGIN_BONUS_PSC:.2f} PSC "
        f"(KES {DAILY_LOGIN_BONUS_KES:.2f})",
        wallet
    )


def _grant_daily_visit_bonus(wallet_addr):
    if not wallet_addr:
        return None
    try:
        wallet = get_wallet(wallet_addr)
        if not wallet:
            return None

        today = datetime.now().strftime("%Y-%m-%d")
        if wallet.get("last_visit_bonus_date") == today:
            return wallet

        wallet["daily_login_bonus_psc"] = round(
            float(wallet.get("daily_login_bonus_psc", 0) or 0) + DAILY_LOGIN_BONUS_PSC, 2
        )
        wallet["last_visit_bonus_date"] = today
        wallet["balance"] = _wallet_total(wallet)

        _save_wallet(wallet)
        _admin_merge_wallet(
            address=wallet_addr,
            purchased_psc=wallet.get("wallet_psc", 0),
            bonus_psc=wallet.get("bonus_psc", 0),
            savings_psc=wallet.get("savings_psc", 0),
            deposit_psc=wallet.get("deposit_psc", 0),
        )
        print(f"[PSC VISIT-BONUS] granted {DAILY_LOGIN_BONUS_PSC:.2f} PSC "
              f"to {wallet_addr} (visit).")
        return wallet
    except Exception as e:
        print(f"[PSC VISIT-BONUS] failed for {wallet_addr}: {e}")
        return None


def deduct_wallet_psc(address, amount):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found"

    amount = round(float(amount), 2)
    if wallet["wallet_psc"] < amount:
        return (
            False,
            f"Insufficient purchased PSC. You have "
            f"{wallet['wallet_psc']:.2f} PSC, need {amount:.2f} PSC."
        )

    wallet["wallet_psc"] = round(wallet["wallet_psc"] - amount, 2)
    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True, "OK"


def deduct_bonus_psc(address, amount):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found"

    amount = round(float(amount), 2)
    if wallet["bonus_psc"] < amount:
        return (
            False,
            f"Insufficient bonus PSC. You have "
            f"{wallet['bonus_psc']:.2f} PSC, need {amount:.2f} PSC."
        )

    wallet["bonus_psc"] = round(wallet["bonus_psc"] - amount, 2)
    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True, "OK"


def calculate_bonus_discount(total_client_kes, available_bonus_psc):
    total_client_kes = max(0.0, float(total_client_kes or 0))
    available_bonus_psc = max(0.0, float(available_bonus_psc or 0))

    requested_discount_psc = round(
        total_client_kes * BONUS_DISCOUNT_RATE / PSC_TO_KES_RATE, 4
    )
    bonus_used_psc = round(
        min(requested_discount_psc, available_bonus_psc), 4
    )
    discount_psc = bonus_used_psc
    discount_kes = round(discount_psc * PSC_TO_KES_RATE, 2)

    return (
        discount_kes,
        discount_psc,
        bonus_used_psc,
        0.0,
    )


def deduct_savings_psc(address, amount):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found"

    amount = round(float(amount), 2)
    if amount <= 0:
        return False, "Savings deduction must be greater than zero."

    available = round(float(wallet.get("savings_psc", 0) or 0), 2)
    if available < amount:
        return (
            False,
            f"Insufficient Savings PSC. You have {available:.2f} PSC, "
            f"need {amount:.2f} PSC."
        )

    wallet["savings_psc"] = round(available - amount, 2)
    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True, "OK"


def partial_deduct_for_shortfall(address, payable_psc, source="bonus"):
    wallet = get_wallet(address)
    if not wallet:
        return {"ok": False, "decline": True, "message": "Wallet not found"}

    payable_psc = round(float(payable_psc or 0), 2)
    source = str(source or "bonus").strip().lower()
    if source not in ("bonus", "savings"):
        source = "bonus"

    if payable_psc <= 0:
        return {
            "ok": True,
            "paid_psc": 0.0,
            "paid_kes": 0.0,
            "remaining_psc": 0.0,
            "remaining_kes": 0.0,
            "source": source,
            "wallet_psc_after": round(float(wallet.get("wallet_psc", 0) or 0), 2),
            "bonus_psc_after": round(float(wallet.get("bonus_psc", 0) or 0), 2),
            "savings_psc_after": round(float(wallet.get("savings_psc", 0) or 0), 2),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
        }

    if source == "savings":
        source_available = round(float(wallet.get("savings_psc", 0) or 0), 2)
        source_label = "Savings"
    else:
        source_available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
        source_label = "Purchased"

    if source_available <= 0:
        return {
            "ok": False,
            "decline": True,
            "source": source,
            "message": (
                f"You have no {source_label} PSC available for payment. "
                "Please top up before ordering."
            ),
            "payable_psc": payable_psc,
            "payable_kes": round(payable_psc * PSC_TO_KES_RATE, 2),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
        }

    paid = round(min(source_available, payable_psc), 2)

    if paid > 0:
        if source == "savings":
            ok, msg = deduct_savings_psc(address, paid)
        else:
            ok, msg = deduct_wallet_psc(address, paid)
        if not ok:
            return {"ok": False, "message": msg}

    wallet = get_wallet(address)
    remaining_psc = round(max(payable_psc - paid, 0.0), 2)
    remaining_kes = round(remaining_psc * PSC_TO_KES_RATE, 2)

    return {
        "ok": True,
        "paid_psc": paid,
        "paid_kes": round(paid * PSC_TO_KES_RATE, 2),
        "remaining_psc": remaining_psc,
        "remaining_kes": remaining_kes,
        "source": source,
        "wallet_psc_after": round(float(wallet.get("wallet_psc", 0) or 0), 2) if wallet else 0.0,
        "bonus_psc_after": round(float(wallet.get("bonus_psc", 0) or 0), 2) if wallet else 0.0,
        "savings_psc_after": round(float(wallet.get("savings_psc", 0) or 0), 2) if wallet else 0.0,
        "psc_to_kes_rate": PSC_TO_KES_RATE,
    }


def deduct_balance(address, amount):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found"

    amount = round(float(amount), 2)
    if amount <= 0:
        return False, "Deduction amount must be greater than zero."

    available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
    if available < amount:
        return False, f"Insufficient purchased PSC. You have {available:.2f} PSC"

    wallet["wallet_psc"] = round(available - amount, 2)
    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True, "OK"


def markup_for(name, category):
    text = f"{name} {category}".lower()
    for kw, mk in CATEGORY_MARKUPS.items():
        if kw in text:
            return mk
    return MARKUP_DEFAULT


# ---------- CATEGORY GROUPING ----------

CATEGORY_GROUPS = [
    {"key": "phones", "label": "Phones & Tablets", "query": "smartphone", "emoji": ""},
    {"key": "tv", "label": "TVs & Audio", "query": "smart tv", "emoji": ""},
    {"key": "appliances", "label": "Appliances", "query": "home appliance", "emoji": ""},
    {"key": "health", "label": "Health & Beauty", "query": "beauty products", "emoji": ""},
    {"key": "home", "label": "Home & Office", "query": "home kitchen", "emoji": ""},
    {"key": "fashion", "label": "Fashion", "query": "fashion", "emoji": ""},
    {"key": "computing", "label": "Computing", "query": "laptop", "emoji": ""},
    {"key": "gaming", "label": "Gaming", "query": "gaming console", "emoji": ""},
    {"key": "groceries", "label": "Groceries", "query": "groceries", "emoji": ""},
    {"key": "baby", "label": "Baby Products", "query": "baby products", "emoji": ""},
    {"key": "sports", "label": "Sporting Goods", "query": "sports equipment", "emoji": ""},
    {"key": "books", "label": "Books", "query": "books", "emoji": ""},
    {"key": "food", "label": "Food & Pantry", "query": "food", "emoji": ""},
    {"key": "unga", "label": "Unga & Flour", "query": "flour", "emoji": ""},
    {"key": "sugar", "label": "Sugar & Sweeteners", "query": "sugar", "emoji": ""},
    {"key": "rice", "label": "Rice & Grains", "query": "rice", "emoji": ""},
    {"key": "cooking_oil", "label": "Cooking Oil", "query": "cooking oil", "emoji": ""},
    {"key": "cereals", "label": "Cereals & Breakfast", "query": "cereal", "emoji": ""},
    {"key": "snacks", "label": "Snacks & Biscuits", "query": "biscuits", "emoji": ""},
    {"key": "beverages", "label": "Beverages & Drinks", "query": "drinks", "emoji": ""},
    {"key": "dairy", "label": "Dairy & Eggs", "query": "milk", "emoji": ""},
    {"key": "meat", "label": "Meat & Fish", "query": "chicken", "emoji": ""},
    {"key": "vegetables", "label": "Vegetables & Fruits", "query": "vegetables", "emoji": ""},
    {"key": "spices", "label": "Spices & Condiments", "query": "spices", "emoji": ""},
    {"key": "canned", "label": "Canned & Packaged", "query": "canned beans", "emoji": ""},
]

FALLBACK_CATEGORY_IMAGES = {
    "phones": "https://images.unsplash.com/photo-1511707171634-5f897ff02aa9?w=400",
    "tv": "https://images.unsplash.com/photo-1593359677879-a4bb92f829d1?w=400",
    "appliances": "https://images.unsplash.com/photo-1556909212-d5b604d0c90d?w=400",
    "health": "https://images.unsplash.com/photo-1596462502278-27bfdc403348?w=400",
    "home": "https://images.unsplash.com/photo-1556909114-f6e7ad7d3136?w=400",
    "fashion": "https://images.unsplash.com/photo-1445205170230-053b83016050?w=400",
    "computing": "https://images.unsplash.com/photo-1517336714731-489689fd1ca8?w=400",
    "gaming": "https://images.unsplash.com/photo-1493711662062-fa541adb3fc8?w=400",
    "groceries": "https://images.unsplash.com/photo-1542838132-92c53300491e?w=400",
    "baby": "https://images.unsplash.com/photo-1519689680058-324335c77eba?w=400",
    "sports": "https://images.unsplash.com/photo-1461896836934-ffe607ba8211?w=400",
    "books": "https://images.unsplash.com/photo-1512820790803-83ca734da794?w=400",
    "food": "https://images.unsplash.com/photo-1504674900247-0877df9cc836?w=400",
    "unga": "https://images.unsplash.com/photo-1509440159596-0249088772ff?w=400",
    "sugar": "https://images.unsplash.com/photo-1581441363689-1f3c3c414635?w=400",
    "rice": "https://images.unsplash.com/photo-1586201375761-83865001e31c?w=400",
    "cooking_oil": "https://images.unsplash.com/photo-1474979266404-7eaacbcd87c5?w=400",
    "cereals": "https://images.unsplash.com/photo-1517686469429-8bdb88b9f907?w=400",
    "snacks": "https://images.unsplash.com/photo-1558961363-fa8fdf82db35?w=400",
    "beverages": "https://images.unsplash.com/photo-1544145945-f90425340c7e?w=400",
    "dairy": "https://images.unsplash.com/photo-1550583724-b2692b85b150?w=400",
    "meat": "https://images.unsplash.com/photo-1607623814075-e51df1bdc82f?w=400",
    "vegetables": "https://images.unsplash.com/photo-1540420773420-3366772f4999?w=400",
    "spices": "https://images.unsplash.com/photo-1596040033229-a9821ebd058d?w=400",
    "canned": "https://images.unsplash.com/photo-1584473457493-17c4c24290c8?w=400",
}

# Automatically attach fallback images to categories for the frontend
for _cat in CATEGORY_GROUPS:
    if "image" not in _cat or not _cat["image"]:
        _cat["image"] = FALLBACK_CATEGORY_IMAGES.get(_cat["key"], "")


# ---------- PRODUCT SOURCES ----------

_JUMIA_REQUESTS_BLOCKED_UNTIL = 0.0
_JUMIA_REQUESTS_BLOCK_SECONDS = 0  # Always try immediately


def _scrape_jumia(q, headers):
    global _JUMIA_REQUESTS_BLOCKED_UNTIL, _PSC_PROXY_DEAD_UNTIL
    import requests as _req
    from bs4 import BeautifulSoup as _BS

    url = (f"https://www.jumia.co.ke{q}" if q.startswith("/")
           else f"https://www.jumia.co.ke/catalog/?q={quote_plus(q)}")

    if True:  # Always attempt the fast requests method first
        try:
            proxy_dict = _requests_proxy_config()
            resp = _req.get(url, headers=headers, timeout=15, proxies=proxy_dict)
            if resp.status_code == 403:
                _JUMIA_REQUESTS_BLOCKED_UNTIL = time.time() + _JUMIA_REQUESTS_BLOCK_SECONDS
                print(f"[PSC SCRAPE] Jumia 403; requests path disabled for {_JUMIA_REQUESTS_BLOCK_SECONDS}s")
            elif resp.status_code == 200:
                soup = _BS(resp.text, "html.parser")
                cards = (soup.select("article.prd")
                         or soup.select("article.-pvxs")
                         or soup.select("article[data-catalog-product]")
                         or soup.select("article[data-ga4-item_id]"))
                print(f"[PSC SCRAPE] Jumia matched {len(cards)} cards (requests) for '{q}'")
                products = []
                for i, card in enumerate(cards[:30], start=1):
                    try:
                        name = card.get("data-moengage-product_name")
                        if not name:
                            nt = card.select_one(".name") or card.select_one("h3")
                            name = nt.get_text(strip=True) if nt else ""
                        if not name: continue
                        price_raw = card.get("data-ga4-price") or card.get("data-moengage-product_price")
                        if not price_raw:
                            pt = card.select_one(".prc")
                            if pt: price_raw = pt.get_text(strip=True).replace("KSh","").replace(",","").strip()
                        if not price_raw: continue
                        try: kes_price = float(str(price_raw).replace(",","").strip())
                        except ValueError: continue
                        if kes_price < 1: continue
                        img_url = card.get("data-moengage-product_image", "")
                        if not img_url:
                            it = card.select_one("img")
                            if it: img_url = it.get("data-src") or it.get("src") or ""
                        category = card.get("data-ga4-item_category") or "Jumia"
                        am = markup_for(name, category)
                        products.append({
                            "id": i, "name": name,
                            "price": round((kes_price / PSC_TO_KES_RATE) * (1 + am), 2),
                            "kes_price": kes_price,
                            "client_kes": round(kes_price * (1 + am), 2),
                            "category": category, "description": name[:60],
                            "image": img_url, "markup": am, "source": "Jumia",
                        })
                    except Exception:
                        continue
                if products:
                    print(f"[PSC SCRAPE] Jumia returned {len(products)} products (requests) for '{q}'")
                    return products
        except Exception as e:
            print(f"Jumia requests error: {e}")
            if "402" in str(e) or "Tunnel connection failed" in str(e) or "ProxyError" in str(e):
                print("[PSC] Requests proxy dead (402). Bypassing proxy for 1 hour...")
                _PSC_PROXY_DEAD_UNTIL = time.time() + 3600
            if "402" in str(e) or "Tunnel connection failed" in str(e) or "ProxyError" in str(e):
                print("[PSC] Requests proxy dead (402). Bypassing proxy for 1 hour...")
                _PSC_PROXY_DEAD_UNTIL = time.time() + 3600

    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                proxy=_playwright_proxy_config(),
                args=[
                    "--disable-blink-features=AutomationControlled",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--single-process",
                    "--no-zygote",
                    "--disable-accelerated-2d-canvas",
                    "--disable-setuid-sandbox",
                    "--js-flags=--max-old-space-size=128"
                ],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script('''
                Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
                Object.defineProperty(navigator, 'languages', { get: () => ['en-KE', 'en-US', 'en'] });
                Object.defineProperty(navigator, 'plugins', { get: () => [1, 2, 3, 4, 5] });
                window.chrome = { runtime: {} };
            ''')
            try: page.goto(url, wait_until="domcontentloaded", timeout=25000)
            except Exception: pass
            page.wait_for_timeout(5000)
            try: page.wait_for_selector("article.prd, article.-pvxs, article[data-catalog-product]", timeout=25000)
            except Exception: pass
            cards = page.query_selector_all("article.prd")
            if not cards: cards = page.query_selector_all("article.-pvxs")
            if not cards: cards = page.query_selector_all("article[data-catalog-product]")
            print(f"[PSC SCRAPE] Jumia matched {len(cards)} cards (Playwright) for '{q}'")
            for i, card in enumerate(cards[:30], start=1):
                try:
                    name = card.get_attribute("data-moengage-product_name") or ""
                    if not name:
                        ne = card.query_selector(".name") or card.query_selector("h3")
                        name = ne.inner_text().strip() if ne else ""
                    if not name: continue
                    price_raw = card.get_attribute("data-ga4-price") or card.get_attribute("data-moengage-product_price")
                    if not price_raw:
                        pe = card.query_selector(".prc")
                        if pe: price_raw = pe.inner_text().replace("KSh","").replace(",","").strip()
                    if not price_raw: continue
                    try: kes_price = float(str(price_raw).replace(",","").strip())
                    except ValueError: continue
                    if kes_price < 1: continue
                    ie = card.query_selector("img")
                    img_url = ""
                    if ie: img_url = ie.get_attribute("data-src") or ie.get_attribute("src") or ""
                    category = card.get_attribute("data-ga4-item_category") or "Jumia"
                    am = markup_for(name, category)
                    products.append({
                        "id": i, "name": name,
                        "price": round((kes_price / PSC_TO_KES_RATE) * (1 + am), 2),
                        "kes_price": kes_price,
                        "client_kes": round(kes_price * (1 + am), 2),
                        "category": category, "description": name[:60],
                        "image": img_url, "markup": am, "source": "Jumia",
                    })
                except Exception:
                    continue
            browser.close()
        if products:
            print(f"[PSC SCRAPE] Jumia returned {len(products)} products (Playwright) for '{q}'")
            return products
        print(f"[PSC SCRAPE] Jumia produced 0 products for '{q}'")
    except Exception as e:
        print(f"Jumia Playwright error: {e}")
    return []


def _scrape_kilimall(q, headers):
    global _PSC_PROXY_DEAD_UNTIL
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                proxy=_playwright_proxy_config(),
                args=[
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--single-process",
                    "--no-zygote",
                    "--js-flags=--max-old-space-size=128"
                ],
            )
            page = browser.new_page(user_agent=headers["User-Agent"])
            page.goto(f"https://www.kilimall.co.ke/search?q={quote_plus(q)}",
                      wait_until="networkidle", timeout=25000)
            try:
                page.wait_for_selector("div.product-item img[src]", timeout=25000)
            except Exception:
                pass
            cards = page.query_selector_all("div.product-item")[:20]
            for i, card in enumerate(cards, start=1):
                try:
                    name = card.query_selector(".product-title").inner_text()
                    price_text = card.query_selector(".product-price").inner_text()
                    img_el = card.query_selector("img")
                    img_url = img_el.get_attribute("src") if img_el else ""
                    if img_url and img_url.startswith("data:image"):
                        img_url = img_el.get_attribute("data-src") or img_url
                    if img_url and img_url.startswith("//"):
                        img_url = "https:" + img_url
                    elif img_url and img_url.startswith("/"):
                        img_url = "https://www.kilimall.co.ke" + img_url
                except Exception:
                    continue
                price_text = (price_text.replace("KSh","").replace("KES","").replace(",","")
                              .strip().split("-")[0].split(" ")[0].strip())
                try:
                    kes_price = float(price_text)
                except ValueError:
                    continue
                category = "Kilimall"
                applied_markup = markup_for(name, category)
                psc_price = round((kes_price / PSC_TO_KES_RATE) * (1 + applied_markup), 2)
                client_kes = round(kes_price * (1 + applied_markup), 2)
                products.append({
                    "id": i, "name": name, "price": psc_price,
                    "kes_price": kes_price, "client_kes": client_kes,
                    "category": category, "description": name[:60],
                    "image": img_url, "markup": applied_markup, "source": "Kilimall",
                })
            browser.close()
        if products:
            print(f"[PSC SCRAPE] Kilimall returned {len(products)} products for '{q}'")
            return products
        print(f"[PSC SCRAPE] Kilimall produced 0 products for '{q}'")
    except Exception as e:
        print(f"Kilimall scrape error: {e}")
        if "ERR_TUNNEL" in str(e) or "proxy" in str(e).lower():
            _PSC_PROXY_DEAD_UNTIL = time.time() + 3600
            print("[PSC] Disabling proxy for 1 hour due to Kilimall tunnel error.")
    return []


def _scrape_carrefour(q):
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                proxy=_playwright_proxy_config(),
                args=[
                    "--disable-blink-features=AutomationControlled",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--single-process",
                    "--no-zygote",
                    "--disable-accelerated-2d-canvas",
                    "--disable-setuid-sandbox",
                    "--js-flags=--max-old-space-size=128"
                ],
            )
            page = browser.new_page(
                user_agent=("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                            "AppleWebKit/537.36 (KHTML, like Gecko) "
                            "Chrome/140.0.0.0 Safari/537.36"),
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script('''
                Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
                Object.defineProperty(navigator, 'languages', { get: () => ['en-KE', 'en-US', 'en'] });
                Object.defineProperty(navigator, 'plugins', { get: () => [1, 2, 3, 4, 5] });
                window.chrome = { runtime: {} };
            ''')
            try:
                page.goto(
                    f"https://www.carrefour.ke/mafken/en/search?keyword={quote_plus(q)}",
                    wait_until="domcontentloaded", timeout=15000,
                )
            except Exception:
                pass
            page.wait_for_timeout(3500)
            for sel in ("button:has-text('Accept All Cookies')",
                        "button:has-text('Accept All')",
                        "button.cc-allow",
                        "button:has-text('Accept')"):
                try:
                    btn = page.query_selector(sel)
                    if btn and btn.is_visible():
                        btn.click(timeout=2000)
                        page.wait_for_timeout(800)
                        break
                except Exception:
                    continue
            try:
                page.wait_for_selector(
                    "a[href*='/p/'], a[href*='/product'], article.product",
                    timeout=25000)
            except Exception:
                pass
            cards = page.query_selector_all("a[href*='/p/']")
            if not cards:
                cards = page.query_selector_all("a[href*='/product']")
            if not cards:
                cards = page.query_selector_all("article.product")
            if not cards:
                cards = page.query_selector_all("[data-testid*='product']")
            print(f"[PSC SCRAPE] Carrefour matched {len(cards)} links for '{q}'")
            seen = set()
            for i, card in enumerate(cards, start=1):
                try:
                    ne = card.query_selector("h3, .product-name, [class*='title'], img[alt]")
                    name = ""
                    if ne:
                        name = (ne.get_attribute("alt") or ne.inner_text() or "").strip()
                    if not name:
                        try:
                            name = (card.inner_text() or "").strip().split("\n")[0]
                        except Exception:
                            name = ""
                    if not name or name in seen:
                        continue
                    pe = card.query_selector("[class*='price'], .price")
                    pt = pe.inner_text() if pe else card.inner_text()
                    kes_price = None
                    for line in pt.split("\n"):
                        cleaned = (line.replace("KSh","").replace("KES","").replace("Ksh","")
                                   .replace("kes","").replace(",","").strip().split(" ")[0])
                        try:
                            val = float(cleaned)
                            if val >= 1:
                                kes_price = val
                                break
                        except ValueError:
                            continue
                    if kes_price is None:
                        continue
                    ie = card.query_selector("img")
                    img_url = ""
                    if ie:
                        img_url = ie.get_attribute("src") or ie.get_attribute("data-src") or ""
                    if img_url.startswith("//"):
                        img_url = "https:" + img_url
                    elif img_url.startswith("/"):
                        img_url = "https://www.carrefour.ke" + img_url
                    seen.add(name)
                    category = "Carrefour"
                    applied_markup = markup_for(name, category)
                    psc_price = round((kes_price / PSC_TO_KES_RATE) * (1 + applied_markup), 2)
                    client_kes = round(kes_price * (1 + applied_markup), 2)
                    products.append({
                        "id": i, "name": name, "price": psc_price,
                        "kes_price": kes_price, "client_kes": client_kes,
                        "category": category, "description": name[:60],
                        "image": img_url, "markup": applied_markup, "source": "Carrefour",
                    })
                except Exception:
                    continue
            browser.close()
        if products:
            print(f"[PSC SCRAPE] Carrefour returned {len(products)} products for '{q}'")
            return products
        print(f"[PSC SCRAPE] Carrefour produced 0 products for '{q}'")
    except Exception as e:
        print(f"Carrefour scrape error: {e}")
    return []


def _scrape_jiji(q, headers):
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                proxy=_playwright_proxy_config(),
                args=[
                    "--disable-blink-features=AutomationControlled",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--single-process",
                    "--no-zygote",
                    "--disable-accelerated-2d-canvas",
                    "--disable-setuid-sandbox",
                    "--js-flags=--max-old-space-size=128"
                ],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            try:
                page.goto(f"https://jiji.co.ke/search?query={quote_plus(q)}",
                          wait_until="domcontentloaded", timeout=25000)
            except Exception:
                pass
            page.wait_for_timeout(4000)
            card_selector = None
            for sel in ("div[class*='b-list-advert__gallery__item']",
                        "div[class*='qa-advert-list-item']",
                        "div[class*='advert'] div[class*='item']",
                        "article[class*='advert']",
                        "div[class*='b-advert']"):
                try:
                    page.wait_for_selector(sel, timeout=6000)
                    card_selector = sel
                    break
                except Exception:
                    continue
            cards = (page.query_selector_all(card_selector) if card_selector
                     else page.query_selector_all("a[href*='/item/']"))
            seen_titles = set()
            for i, card in enumerate(cards[:30], start=1):
                try:
                    te = (card.query_selector("[class*='b-advert-title']")
                          or card.query_selector("[class*='advert-title']")
                          or card.query_selector("h3") or card.query_selector("h4")
                          or card.query_selector("[class*='title']"))
                    name = te.inner_text().strip() if te else ""
                    if not name:
                        name = (card.get_attribute("aria-label") or card.get_attribute("title") or "").strip()
                    if not name or name.lower() in seen_titles:
                        continue
                    pe = (card.query_selector("[class*='b-advert-price']")
                          or card.query_selector("[class*='advert-price']")
                          or card.query_selector("[class*='price']"))
                    pr = pe.inner_text().strip() if pe else ""
                    pc = (pr.replace("KSh","").replace("Ksh","").replace("KES","")
                          .replace("kes","").replace(",","").replace(" ","").strip())
                    if "neg" in pc.lower():
                        pc = "".join(ch for ch in pc if ch.isdigit() or ch == ".")
                    if not pc:
                        continue
                    try:
                        kes_price = float(pc.split("-")[0])
                    except ValueError:
                        continue
                    if kes_price < 1:
                        continue
                    ie = card.query_selector("img")
                    img_url = ""
                    if ie:
                        img_url = (ie.get_attribute("data-src") or ie.get_attribute("src")
                                   or ie.get_attribute("data-original") or "")
                    if img_url.startswith("//"):
                        img_url = "https:" + img_url
                    elif img_url.startswith("/"):
                        img_url = "https://jiji.co.ke" + img_url
                    seen_titles.add(name.lower())
                    category = "Jiji"
                    applied_markup = markup_for(name, category)
                    psc_price = round((kes_price / PSC_TO_KES_RATE) * (1 + applied_markup), 2)
                    client_kes = round(kes_price * (1 + applied_markup), 2)
                    products.append({
                        "id": i, "name": name, "price": psc_price,
                        "kes_price": kes_price, "client_kes": client_kes,
                        "category": category, "description": name[:60],
                        "image": img_url, "markup": applied_markup,
                        "source": "Jiji", "vendor": "jiji",
                    })
                except Exception:
                    continue
            browser.close()
        if products:
            print(f"[PSC SCRAPE] Jiji returned {len(products)} products for '{q}'")
            return products
        print(f"[PSC SCRAPE] Jiji produced 0 products for '{q}'")
    except Exception as e:
        print(f"Jiji scrape error: {e}")
    return []


def _scrape_woocommerce(q, url_template, source_label, category, headers):
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                proxy=_playwright_proxy_config(),
                args=[
                    "--disable-blink-features=AutomationControlled",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--single-process",
                    "--no-zygote",
                    "--disable-accelerated-2d-canvas",
                    "--disable-setuid-sandbox",
                    "--js-flags=--max-old-space-size=128"
                ],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script('''
                Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
                Object.defineProperty(navigator, 'languages', { get: () => ['en-KE', 'en-US', 'en'] });
                Object.defineProperty(navigator, 'plugins', { get: () => [1, 2, 3, 4, 5] });
                window.chrome = { runtime: {} };
            ''')
            url = url_template.format(q=quote_plus(q))
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=25000)
            except Exception:
                pass
            page.wait_for_timeout(2500)
            for sel in ("ul.products li.product", "li.product",
                        ".product-small", "div.product"):
                try:
                    page.wait_for_selector(sel, timeout=6000)
                    break
                except Exception:
                    continue
            cards = page.query_selector_all("ul.products li.product")
            if not cards:
                cards = page.query_selector_all("li.product")
            if not cards:
                cards = page.query_selector_all("div.product-small")
            print("[PSC SCRAPE] " + source_label + " matched " + str(len(cards)) + " cards for '" + q + "'")
            seen = set()
            for i, card in enumerate(cards[:30], start=1):
                try:
                    ne = (card.query_selector(".woocommerce-loop-product__title")
                          or card.query_selector("h3")
                          or card.query_selector("h2"))
                    name = ne.inner_text().strip() if ne else ""
                    if not name or name.lower() in seen:
                        continue
                    pe = card.query_selector(".price")
                    pt = pe.inner_text() if pe else ""
                    kes_price = None
                    for line in pt.split("\n"):
                        cleaned = (line.replace("KSh","").replace("KES","")
                                   .replace("Ksh","").replace("kes","")
                                   .replace(",","").strip())
                        cleaned = cleaned.split("-")[0].split(" ")[0].strip()
                        try:
                            val = float(cleaned)
                            if val >= 1:
                                kes_price = val
                                break
                        except ValueError:
                            continue
                    if kes_price is None:
                        continue
                    ie = card.query_selector("img")
                    img_url = ""
                    if ie:
                        img_url = (ie.get_attribute("data-src")
                                   or ie.get_attribute("src") or "")
                    if img_url.startswith("//"):
                        img_url = "https:" + img_url
                    seen.add(name.lower())
                    applied_markup = markup_for(name, category)
                    psc_price = round((kes_price / PSC_TO_KES_RATE) * (1 + applied_markup), 2)
                    client_kes = round(kes_price * (1 + applied_markup), 2)
                    products.append({
                        "id": i, "name": name, "price": psc_price,
                        "kes_price": kes_price, "client_kes": client_kes,
                        "category": category, "description": name[:60],
                        "image": img_url, "markup": applied_markup,
                        "source": source_label,
                    })
                except Exception:
                    continue
            browser.close()
        if products:
            print("[PSC SCRAPE] " + source_label + " returned " + str(len(products)) + " products for '" + q + "'")
            return products
        print("[PSC SCRAPE] " + source_label + " produced 0 products for '" + q + "'")
    except Exception as e:
        print(source_label + " scrape error: " + str(e))
    return []


def _scrape_magento(q, url_template, source_label, category, headers):
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                proxy=_playwright_proxy_config(),
                args=[
                    "--disable-blink-features=AutomationControlled",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--single-process",
                    "--no-zygote",
                    "--disable-accelerated-2d-canvas",
                    "--disable-setuid-sandbox",
                    "--js-flags=--max-old-space-size=128"
                ],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script('''
                Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
                Object.defineProperty(navigator, 'languages', { get: () => ['en-KE', 'en-US', 'en'] });
                Object.defineProperty(navigator, 'plugins', { get: () => [1, 2, 3, 4, 5] });
                window.chrome = { runtime: {} };
            ''')
            url = url_template.format(q=quote_plus(q))
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=25000)
            except Exception:
                pass
            page.wait_for_timeout(5000)
            try:
                page.wait_for_selector(
                    "li.product-item, .product-item-info, ol.products li, "
                    ".product-item, article.product, .product-card",
                    timeout=25000)
            except Exception:
                pass
            cards = page.query_selector_all("li.product-item")
            if not cards:
                cards = page.query_selector_all(".product-item-info")
            if not cards:
                cards = page.query_selector_all("ol.products li")
            if not cards:
                cards = page.query_selector_all("article.product")
            if not cards:
                cards = page.query_selector_all(".product-card")
            print("[PSC SCRAPE] " + source_label + " matched " + str(len(cards)) + " cards for '" + q + "'")
            seen = set()
            for i, card in enumerate(cards[:30], start=1):
                try:
                    ne = (card.query_selector(".product-item-link")
                          or card.query_selector(".product-item-name a")
                          or card.query_selector("h3")
                          or card.query_selector("h2")
                          or card.query_selector("a[title]"))
                    name = ""
                    if ne:
                        name = (ne.inner_text() or ne.get_attribute("title") or "").strip()
                    if not name or name.lower() in seen:
                        continue
                    pe = card.query_selector(".price")
                    pt = pe.inner_text() if pe else ""
                    kes_price = None
                    for line in pt.split("\n"):
                        cleaned = (line.replace("KSh","").replace("KES","")
                                   .replace("Ksh","").replace("kes","")
                                   .replace(",","").strip())
                        cleaned = (cleaned.replace("From","").strip()
                                   .split("-")[0].split(" ")[0].strip())
                        try:
                            val = float(cleaned)
                            if val >= 1:
                                kes_price = val
                                break
                        except ValueError:
                            continue
                    if kes_price is None:
                        continue
                    ie = card.query_selector("img")
                    img_url = ""
                    if ie:
                        img_url = (ie.get_attribute("data-src")
                                   or ie.get_attribute("src") or "")
                    if img_url.startswith("//"):
                        img_url = "https:" + img_url
                    seen.add(name.lower())
                    applied_markup = markup_for(name, category)
                    psc_price = round((kes_price / PSC_TO_KES_RATE) * (1 + applied_markup), 2)
                    client_kes = round(kes_price * (1 + applied_markup), 2)
                    products.append({
                        "id": i, "name": name, "price": psc_price,
                        "kes_price": kes_price, "client_kes": client_kes,
                        "category": category, "description": name[:60],
                        "image": img_url, "markup": applied_markup,
                        "source": source_label,
                    })
                except Exception:
                    continue
            browser.close()
        if products:
            print("[PSC SCRAPE] " + source_label + " returned " + str(len(products)) + " products for '" + q + "'")
            return products
        print("[PSC SCRAPE] " + source_label + " produced 0 products for '" + q + "'")
    except Exception as e:
        print(source_label + " scrape error: " + str(e))
    return []


def _scrape_generic_react(q, url_template, source_label, category, headers):
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                headless=True,
                proxy=_playwright_proxy_config(),
                args=[
                    "--disable-blink-features=AutomationControlled",
                    "--no-sandbox",
                    "--disable-dev-shm-usage",
                    "--disable-gpu",
                    "--single-process",
                    "--no-zygote",
                    "--disable-accelerated-2d-canvas",
                    "--disable-setuid-sandbox",
                    "--js-flags=--max-old-space-size=128"
                ],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script('''
                Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
                Object.defineProperty(navigator, 'languages', { get: () => ['en-KE', 'en-US', 'en'] });
                Object.defineProperty(navigator, 'plugins', { get: () => [1, 2, 3, 4, 5] });
                window.chrome = { runtime: {} };
            ''')
            url = url_template.format(q=quote_plus(q))
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=25000)
            except Exception:
                pass
            page.wait_for_timeout(4500)
            card_selectors = (
                "[data-testid*='product']", "[class*='product-card']",
                "[class*='ProductCard']", "article[class*='product']",
                "div[class*='product-item']", "a[href*='/product/']",
            )
            cards = []
            for sel in card_selectors:
                try:
                    found = page.query_selector_all(sel)
                    if found:
                        cards = found
                        break
                except Exception:
                    continue
            if not cards:
                print("[PSC SCRAPE] " + source_label + " matched 0 cards for '" + q + "'")
                browser.close()
                return []
            seen = set()
            for i, card in enumerate(cards[:30], start=1):
                try:
                    ne = (card.query_selector("h3, h2, h4")
                          or card.query_selector("[class*='name']")
                          or card.query_selector("[class*='title']"))
                    name = ne.inner_text().strip() if ne else ""
                    if not name:
                        name = (card.get_attribute("aria-label")
                                or card.get_attribute("title") or "").strip()
                    if not name or name.lower() in seen:
                        continue
                    pt = ""
                    pe = (card.query_selector("[class*='price']")
                          or card.query_selector("[data-testid*='price']"))
                    if pe:
                        pt = pe.inner_text()
                    else:
                        pt = card.inner_text()
                    kes_price = None
                    for line in pt.split("\n"):
                        cleaned = (line.replace("KSh","").replace("KES","")
                                   .replace("Ksh","").replace("kes","")
                                   .replace(",","").strip())
                        cleaned = cleaned.split(" ")[0].strip()
                        try:
                            val = float(cleaned)
                            if val >= 1:
                                kes_price = val
                                break
                        except ValueError:
                            continue
                    if kes_price is None:
                        continue
                    ie = card.query_selector("img")
                    img_url = ""
                    if ie:
                        img_url = (ie.get_attribute("src")
                                   or ie.get_attribute("data-src") or "")
                    if img_url.startswith("//"):
                        img_url = "https:" + img_url
                    seen.add(name.lower())
                    applied_markup = markup_for(name, category)
                    psc_price = round((kes_price / PSC_TO_KES_RATE) * (1 + applied_markup), 2)
                    client_kes = round(kes_price * (1 + applied_markup), 2)
                    products.append({
                        "id": i, "name": name, "price": psc_price,
                        "kes_price": kes_price, "client_kes": client_kes,
                        "category": category, "description": name[:60],
                        "image": img_url, "markup": applied_markup,
                        "source": source_label,
                    })
                except Exception:
                    continue
            browser.close()
        if products:
            print("[PSC SCRAPE] " + source_label + " returned " + str(len(products)) + " products for '" + q + "'")
            return products
        print("[PSC SCRAPE] " + source_label + " produced 0 products for '" + q + "'")
    except Exception as e:
        print(source_label + " scrape error: " + str(e))
    return []


def _scrape_fahavi(q, headers):
    return _scrape_woocommerce(
        q, "https://fahavicomputers.co.ke/?s={q}&post_type=product",
        "Fahavi Computers", "Computers", headers)


def _scrape_textbookcentre(q, headers):
    return _scrape_magento(
        q, "https://textbookcentre.com/catalogsearch/result/?q={q}",
        "Text Book Centre", "Books", headers)


def _scrape_naivas(q, headers):
    return _scrape_generic_react(
        q, "https://naivas.co.ke/search?q={q}",
        "Naivas", "Groceries", headers)


def _scrape_vivo(q, headers):
    return _scrape_magento(
        q, "https://vivo.co.ke/catalogsearch/result/?q={q}",
        "Vivo", "Appliances", headers)


def _scrape_copell(q, headers):
    return _scrape_woocommerce(
        q, "https://copell.co.ke/?s={q}&post_type=product",
        "Copell", "Groceries", headers)


def _scrape_masoko(q, headers):
    return _scrape_generic_react(
        q, "https://masoko.co.ke/search?q={q}",
        "Safaricom Masoko", "Phones & TVs", headers)


def _scrape_hotpoint(q, headers):
    return _scrape_magento(
        q, "https://hotpoint.co.ke/catalogsearch/result/?q={q}",
        "Hotpoint Appliances", "TVs & Appliances", headers)


def _scrape_samsungstore(q, headers):
    return _scrape_magento(
        q, "https://samsungbrandstore.co.ke/catalogsearch/result/?q={q}",
        "Samsung Brand Store", "Samsung", headers)


def _scrape_vendors_sequential(query, vendor=None):
    q = str(query or "electronics").strip() or "electronics"
    vendor = str(vendor or "").strip().lower() or None
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
    }

    if vendor in (None, "jumia"):
        p = _scrape_jumia(q, headers)
        if p: return p
    if vendor in (None, "kilimall"):
        p = _scrape_kilimall(q, headers)
        if p: return p
    if vendor in (None, "carrefour"):
        p = _scrape_carrefour(q)
        if p: return p
    if vendor in (None, "jiji"):
        p = _scrape_jiji(q, headers)
        if p: return p
    if vendor in (None, "fahavi"):
        p = _scrape_fahavi(q, headers)
        if p: return p
    if vendor in (None, "textbookcentre"):
        p = _scrape_textbookcentre(q, headers)
        if p: return p
    if vendor in (None, "naivas"):
        p = _scrape_naivas(q, headers)
        if p: return p
    if vendor in (None, "vivo"):
        p = _scrape_vivo(q, headers)
        if p: return p
    if vendor in (None, "copell"):
        p = _scrape_copell(q, headers)
        if p: return p
    if vendor in (None, "masoko"):
        p = _scrape_masoko(q, headers)
        if p: return p
    if vendor in (None, "hotpoint"):
        p = _scrape_hotpoint(q, headers)
        if p: return p
    if vendor in (None, "samsungstore"):
        p = _scrape_samsungstore(q, headers)
        if p: return p

    try:
        with open('products.json', 'r') as f:
            _fb = json.load(f)
        _fbp = (_fb or {}).get('products', []) or []
        if _fbp:
            print(f"[PSC SCRAPE] All vendors empty for '{q}'; serving products.json ({len(_fbp)}).")
            return _fbp
    except Exception:
        pass
    print(f"[PSC SCRAPE] All vendors empty for '{q}'; serving premium fallback.")
    
    # High-quality fallback list with real images so the site NEVER looks empty
    _premium_fallback = [
        {"name": "Samsung Galaxy S23 Ultra 256GB", "price": 1200.0, "kes_price": 120000.0, "category": "Phones & Tablets", "image": "https://images.unsplash.com/photo-1610945265064-0e34e5519bbf?w=400"},
        {"name": "Apple iPhone 14 Pro Max 128GB", "price": 1350.0, "kes_price": 135000.0, "category": "Phones & Tablets", "image": "https://images.unsplash.com/photo-1511707171634-5f897ff02aa9?w=400"},
        {"name": "HP Pavilion 15 Core i7 12th Gen", "price": 850.0, "kes_price": 85000.0, "category": "Computing", "image": "https://images.unsplash.com/photo-1496181133206-80ce9b88a853?w=400"},
        {"name": "Apple MacBook Air M2 13-inch", "price": 1500.0, "kes_price": 150000.0, "category": "Computing", "image": "https://images.unsplash.com/photo-1517336714731-489689fd1ca8?w=400"},
        {"name": "Sony 55 Inch 4K Ultra HD Smart TV", "price": 650.0, "kes_price": 65000.0, "category": "TVs & Audio", "image": "https://images.unsplash.com/photo-1593359677879-a4bb92f829d1?w=400"},
        {"name": "JBL Flip 6 Portable Bluetooth Speaker", "price": 120.0, "kes_price": 12000.0, "category": "TVs & Audio", "image": "https://images.unsplash.com/photo-1608043152269-423dbba4e7e1?w=400"},
        {"name": "LG 43 Inch Smart LED TV", "price": 320.0, "kes_price": 32000.0, "category": "TVs & Audio", "image": "https://images.unsplash.com/photo-1593359677879-a4bb92f829d1?w=400"},
        {"name": "PlayStation 5 Console Disc Edition", "price": 750.0, "kes_price": 75000.0, "category": "Gaming", "image": "https://images.unsplash.com/photo-1606813907291-d86efa9b94db?w=400"},
        {"name": "Nike Air Max 270 Running Shoes", "price": 150.0, "kes_price": 15000.0, "category": "Fashion", "image": "https://images.unsplash.com/photo-1542291026-7eec264c27ff?w=400"},
        {"name": "Biore UV Aqua Rich Watery Essence SPF 50", "price": 25.0, "kes_price": 2500.0, "category": "Health & Beauty", "image": "https://images.unsplash.com/photo-1556228578-0d85b1a4d571?w=400"}
    ]

    # Cycle through to generate 20 products to fill the screen
    products = []
    for i in range(20):
        item = _premium_fallback[i % len(_premium_fallback)]
        products.append({
            "id": 900000 + i,
            "name": item["name"],
            "price": item["price"] + (i * 0.1),
            "kes_price": item["kes_price"] + (i * 10),
            "client_kes": round((item["kes_price"] + (i * 10)) * 1.05, 2),
            "category": item["category"],
            "description": item["name"][:60],
            "image": item["image"],
            "markup": 0.05,
            "source": "PSC Premium",
            "save_more": False
        })
    return products


# ============================================================
# PSC SELLER SUBSYSTEM
# ============================================================

SELLERS_FILE = os.path.join(
    os.path.dirname(CLIENTS_FILE) or ".",
    "seller_registry.json"
)
SELLER_ITEMS_FILE = os.path.join(
    os.path.dirname(CLIENTS_FILE) or ".",
    "seller_items.json"
)


def _load_sellers():
    d = _jload(SELLERS_FILE, {})
    return d if isinstance(d, dict) else {}


def _save_sellers(data):
    _jsave(SELLERS_FILE, data)


def _load_seller_items():
    d = _jload(SELLER_ITEMS_FILE, [])
    return d if isinstance(d, list) else []


def _save_seller_items(items):
    _jsave(SELLER_ITEMS_FILE, items)


def _current_seller():
    phone = session.get("seller_phone", "")
    if not phone:
        return None
    sellers = _load_sellers()
    return sellers.get(phone)


def _seller_items_for_query(query):
    q = str(query or "").strip().lower()
    if not q:
        return []
    q_tokens = [w for w in q.split() if len(w) >= 3] or q.split()

    out = []
    for item in _load_seller_items():
        if item.get("status") != "ACTIVE":
            continue

        cat_q = str(item.get("category_query") or "").strip().lower()
        if cat_q and cat_q == q:
            out.append(item)
            continue

        cat_key = str(item.get("category_key") or "").strip().lower()
        if cat_key and cat_key == q:
            out.append(item)
            continue

        cat_label = str(item.get("category") or "").strip().lower()
        if cat_label and cat_label == q:
            out.append(item)
            continue

        kw_blob = " ".join(str(k) for k in (item.get("keywords") or [])).lower()
        if kw_blob and q_tokens and all(w in kw_blob for w in q_tokens):
            out.append(item)
            continue

        haystack = " ".join([
            str(item.get("name", "")),
            str(item.get("category", "")),
            str(item.get("description", "")),
            str(item.get("category_query", "")),
            str(item.get("category_key", "")),
            kw_blob,
        ]).lower()
        if q_tokens and all(w in haystack for w in q_tokens):
            out.append(item)

    return out


def _build_seller_product(item):
    try:
        kes_price = round(float(item.get("kes_price") or 0), 2)
    except (TypeError, ValueError):
        return None
    if kes_price < 1:
        return None
    psc_price = round(kes_price / PSC_TO_KES_RATE, 2)
    return {
        "id": item.get("id"),
        "name": str(item.get("name") or "Seller Item"),
        "price": psc_price,
        "kes_price": kes_price,
        "client_kes": kes_price,
        "category": str(item.get("category") or "Seller"),
        "description": str(item.get("description") or item.get("name") or "")[:60],
        "image": str(item.get("image") or ""),
        "markup": 0.0,
        "source": "Seller",
        "save_more": False,
    }


import mimetypes as _mimetypes
from urllib.parse import urlparse as _urlparse

SELLER_IMAGE_DIR = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "static", "seller_images"
)
try:
    os.makedirs(SELLER_IMAGE_DIR, exist_ok=True)
except Exception as _e:
    print("[SELLER IMG] could not create folder: " + str(_e))

SELLER_IMAGE_MAX_BYTES = 5 * 1024 * 1024
SELLER_IMAGE_ALLOWED_EXT = {".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".svg"}


def _localize_seller_image(src):
    src = str(src or "").strip()
    if not src:
        return ""
    if src.startswith("/static/") or src.startswith("/uploads/"):
        return src
    if not (src.startswith("http://") or src.startswith("https://")):
        return src
    try:
        import requests as _rq
        resp = _rq.get(src, timeout=15, stream=True,
                       headers={"User-Agent": "Mozilla/5.0"})
        if resp.status_code != 200:
            print("[SELLER IMG] fetch HTTP " + str(resp.status_code) + " for " + src[:80])
            return src
        ctype = (resp.headers.get("Content-Type") or "").lower().split(";")[0].strip()
        ext = ""
        if ctype:
            for k, v in _mimetypes.types_map.items():
                if v == ctype:
                    ext = k.lower()
                    break
        if not ext or ext not in SELLER_IMAGE_ALLOWED_EXT:
            uext = os.path.splitext(_urlparse(src).path)[1].lower()
            if uext in SELLER_IMAGE_ALLOWED_EXT:
                ext = uext
            else:
                ext = ".jpg"
        fname = uuid.uuid4().hex + ext
        dest = os.path.join(SELLER_IMAGE_DIR, fname)
        total = 0
        with open(dest, "wb") as f:
            for chunk in resp.iter_content(8192):
                if not chunk:
                    continue
                total += len(chunk)
                if total > SELLER_IMAGE_MAX_BYTES:
                    break
                f.write(chunk)
        if total > SELLER_IMAGE_MAX_BYTES:
            try:
                os.remove(dest)
            except Exception:
                pass
            print("[SELLER IMG] too large for " + src[:80])
            return src
        return "/static/seller_images/" + fname
    except Exception as e:
        print("[SELLER IMG] localize failed: " + str(e))
        return src


@app.route("/api/seller/upload_image", methods=["POST"])
def api_seller_upload_image():
    try:
        seller = _current_seller()
        if not seller:
            return jsonify({"success": False,
                            "message": "Please log in as a seller first."}), 401
        if "image" not in request.files:
            return jsonify({"success": False,
                            "message": "No file uploaded."}), 400
        f = request.files["image"]
        if not f or not f.filename:
            return jsonify({"success": False,
                            "message": "Empty file."}), 400
        _, ext = os.path.splitext(f.filename)
        ext = (ext or "").lower()
        if ext not in SELLER_IMAGE_ALLOWED_EXT:
            return jsonify({"success": False,
                            "message": "File type not allowed. Use JPG, PNG, GIF, WEBP or SVG."}), 400
        data = f.read()
        if len(data) > SELLER_IMAGE_MAX_BYTES:
            return jsonify({"success": False,
                            "message": "File too large. Max 5 MB."}), 400
        if len(data) == 0:
            return jsonify({"success": False,
                            "message": "Empty file."}), 400
        fname = uuid.uuid4().hex + ext
        dest = os.path.join(SELLER_IMAGE_DIR, fname)
        with open(dest, "wb") as out:
            out.write(data)
        print("[SELLER IMG] uploaded " + fname + " (" + str(len(data)) + " bytes)")
        return jsonify({
            "success": True,
            "url": "/static/seller_images/" + fname,
            "message": "Image uploaded.",
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/sell")
def sell_page():
    return render_template("seller.html")


@app.route("/api/seller/register", methods=["POST"])
def api_seller_register():
    try:
        data = request.get_json() or {}
        name          = (data.get("name") or "").strip()
        phone         = (data.get("phone") or "").strip()
        email         = (data.get("email") or "").strip()
        password      = (data.get("password") or "").strip()
        business_name = (data.get("business_name") or "").strip()

        if not name or not phone or not password:
            return jsonify({"success": False,
                            "message": "Name, phone and password are required."}), 400

        key = _normalize_phone(phone)
        if not key or len(key) < 9:
            return jsonify({"success": False,
                            "message": "Enter a valid phone number."}), 400
        if len(password) < 4:
            return jsonify({"success": False,
                            "message": "Password must be at least 4 characters."}), 400

        sellers = _load_sellers()
        if key in sellers and sellers[key].get("password"):
            return jsonify({"success": False,
                            "message": "A seller account with this phone already exists. Please log in."}), 400

        sellers[key] = {
            "phone":         key,
            "name":          name,
            "business_name": business_name or name,
            "email":         email,
            "password":      generate_password_hash(password),
            "registered_at": _now(),
            "status":        "ACTIVE",
        }
        _save_sellers(sellers)

        session["seller_phone"] = key
        session.permanent = True

        return jsonify({
            "success": True,
            "message": "Seller account created.",
            "seller": {
                "phone":         key,
                "name":          name,
                "business_name": sellers[key]["business_name"],
                "email":         email,
            },
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/seller/login", methods=["POST"])
def api_seller_login():
    try:
        data     = request.get_json() or {}
        phone    = (data.get("phone") or "").strip()
        password = (data.get("password") or "").strip()

        if not phone or not password:
            return jsonify({"success": False,
                            "message": "Phone and password are required."}), 400

        key = _normalize_phone(phone)
        sellers = _load_sellers()
        seller = sellers.get(key)
        if not seller:
            return jsonify({"success": False,
                            "message": "No seller account found for this phone."}), 404
        if seller.get("status") != "ACTIVE":
            return jsonify({"success": False,
                            "message": "This seller account is not active."}), 403

        try:
            ok = check_password_hash(seller.get("password", ""), password)
        except Exception:
            ok = False
        if not ok:
            return jsonify({"success": False,
                            "message": "Incorrect password."}), 401

        session["seller_phone"] = key
        session.permanent = True

        return jsonify({
            "success": True,
            "message": "Logged in.",
            "seller": {
                "phone":         key,
                "name":          seller.get("name", ""),
                "business_name": seller.get("business_name", ""),
                "email":         seller.get("email", ""),
            },
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/seller/logout", methods=["POST"])
def api_seller_logout():
    session.pop("seller_phone", None)
    session.modified = True
    return jsonify({"success": True, "message": "Logged out."})


@app.route("/api/seller/me", methods=["GET"])
def api_seller_me():
    seller = _current_seller()
    if not seller:
        return jsonify({"success": False, "logged_in": False})
    return jsonify({
        "success": True,
        "logged_in": True,
        "seller": {
            "phone":         seller.get("phone", ""),
            "name":          seller.get("name", ""),
            "business_name": seller.get("business_name", ""),
            "email":         seller.get("email", ""),
        },
    })


@app.route("/api/seller/items", methods=["POST"])
def api_seller_items_add():
    try:
        seller = _current_seller()
        if not seller:
            return jsonify({"success": False,
                            "message": "Please log in as a seller first."}), 401

        data = request.get_json() or {}
        name = (data.get("name") or "").strip()
        try:
            kes_price = round(float(data.get("kes_price") or 0), 2)
        except (TypeError, ValueError):
            kes_price = 0.0
        category    = (data.get("category") or "Other").strip()
        description = (data.get("description") or "").strip()
        image       = _localize_seller_image(data.get("image") or "")

        if not name:
            return jsonify({"success": False,
                            "message": "Product name is required."}), 400
        if len(name) > 200:
            return jsonify({"success": False,
                            "message": "Product name is too long."}), 400
        if kes_price < 1:
            return jsonify({"success": False,
                            "message": "Price must be at least KES 1."}), 400
        if kes_price > 10_000_000:
            return jsonify({"success": False,
                            "message": "Price is too high."}), 400

        auto_kw = []
        matched_cat_key = ""
        matched_cat_query = ""
        matched_cat_label = category
        for cg in CATEGORY_GROUPS:
            if (cg["label"].lower() == category.lower()
                    or cg["key"].lower() == category.lower()):
                auto_kw.append(cg["query"])
                matched_cat_key = cg["key"]
                matched_cat_query = cg["query"]
                matched_cat_label = cg["label"]
                break

        keywords = data.get("keywords") or []
        if not isinstance(keywords, list):
            keywords = [str(keywords)]
        keywords = [str(k).strip() for k in keywords if str(k).strip()] + auto_kw

        item_id = _stable_product_id(name, "Seller", matched_cat_label, kes_price)

        items = _load_seller_items()
        items.append({
            "id":              item_id,
            "seller_phone":    seller.get("phone", ""),
            "seller_name":     seller.get("business_name") or seller.get("name", ""),
            "name":            name,
            "description":     description,
            "category":        matched_cat_label,
            "category_key":    matched_cat_key,
            "category_query":  matched_cat_query,
            "kes_price":       kes_price,
            "image":           image,
            "keywords":        keywords,
            "status":          "ACTIVE",
            "created_at":      _now(),
        })
        _save_seller_items(items)

        try:
            _cache_clear()
            _save_disk_cache(force=True)
        except Exception:
            pass

        return jsonify({"success": True, "message": "Item listed."})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/seller/items", methods=["GET"])
def api_seller_items_list():
    seller = _current_seller()
    if not seller:
        return jsonify({"success": False, "message": "Not logged in."}), 401
    phone = seller.get("phone", "")
    mine = [i for i in _load_seller_items() if i.get("seller_phone") == phone]
    return jsonify({"success": True, "items": mine})


@app.route("/api/seller/items/<int:item_id>", methods=["DELETE"])
def api_seller_items_delete(item_id):
    seller = _current_seller()
    if not seller:
        return jsonify({"success": False, "message": "Not logged in."}), 401
    phone = seller.get("phone", "")
    items = _load_seller_items()
    kept = [i for i in items if not (i.get("id") == item_id and i.get("seller_phone") == phone)]
    if len(kept) == len(items):
        return jsonify({"success": False, "message": "Item not found."}), 404
    _save_seller_items(kept)
    try:
        _cache_clear()
        _save_disk_cache(force=True)
    except Exception:
        pass
    return jsonify({"success": True, "message": "Item removed."})


def _fallback_products(category_label="Sample"):
    # Curated fallback products that look realistic and professional
    _curated_items = [
        {"name": "PlayStation 5 Console Disc Edition", "price": 750.0, "kes_price": 75000.0, "category": "Gaming", "image": "https://images.unsplash.com/photo-1606813907291-d86efa9b94db?w=400"},
        {"name": "Xbox Series X 1TB Console", "price": 650.0, "kes_price": 65000.0, "category": "Gaming", "image": "https://images.unsplash.com/photo-1621259182978-fbf93132d53d?w=400"},
        {"name": "Samsung Galaxy S23 Ultra 256GB", "price": 1200.0, "kes_price": 120000.0, "category": "Phones & Tablets", "image": "https://images.unsplash.com/photo-1610945265064-0e34e5519bbf?w=400"},
        {"name": "Apple iPhone 14 Pro Max 128GB", "price": 1350.0, "kes_price": 135000.0, "category": "Phones & Tablets", "image": "https://images.unsplash.com/photo-1511707171634-5f897ff02aa9?w=400"},
        {"name": "HP Pavilion 15 Core i7 12th Gen", "price": 850.0, "kes_price": 85000.0, "category": "Computing", "image": "https://images.unsplash.com/photo-1496181133206-80ce9b88a853?w=400"},
        {"name": "Apple MacBook Air M2 13-inch", "price": 1500.0, "kes_price": 150000.0, "category": "Computing", "image": "https://images.unsplash.com/photo-1517336714731-489689fd1ca8?w=400"},
        {"name": "Sony 55 Inch 4K Ultra HD Smart TV", "price": 650.0, "kes_price": 65000.0, "category": "TVs & Audio", "image": "https://images.unsplash.com/photo-1593359677879-a4bb92f829d1?w=400"},
        {"name": "JBL Flip 6 Portable Bluetooth Speaker", "price": 120.0, "kes_price": 12000.0, "category": "TVs & Audio", "image": "https://images.unsplash.com/photo-1608043152269-423dbba4e7e1?w=400"},
        {"name": "Nike Air Max 270 Running Shoes", "price": 150.0, "kes_price": 15000.0, "category": "Fashion", "image": "https://images.unsplash.com/photo-1542291026-7eec264c27ff?w=400"},
        {"name": "Biore UV Aqua Rich Watery Essence SPF 50", "price": 25.0, "kes_price": 2500.0, "category": "Health & Beauty", "image": "https://images.unsplash.com/photo-1556228578-0d85b1a4d571?w=400"},
        {"name": "Dyson V15 Detect Cordless Vacuum", "price": 700.0, "kes_price": 70000.0, "category": "Appliances", "image": "https://images.unsplash.com/photo-1558317374-067fb5f30001?w=400"},
        {"name": "LG 2-Door Fridge 340L", "price": 500.0, "kes_price": 50000.0, "category": "Appliances", "image": "https://images.unsplash.com/photo-1584622650111-993a426fbf0a?w=400"},
        {"name": "Nescafe Gold Blend Instant Coffee 200g", "price": 15.0, "kes_price": 1500.0, "category": "Groceries", "image": "https://images.unsplash.com/photo-1559525839-b184a4d698c7?w=400"},
        {"name": "Pampers Baby Dry Diapers Size 3", "price": 30.0, "kes_price": 3000.0, "category": "Baby Products", "image": "https://images.unsplash.com/photo-1555252333-9f8e92e65df9?w=400"},
        {"name": "Wilson NBA Authentic Basketball", "price": 45.0, "kes_price": 4500.0, "category": "Sporting Goods", "image": "https://images.unsplash.com/photo-1519861531473-9200262188bf?w=400"},
        {"name": "Atomic Habits by James Clear", "price": 20.0, "kes_price": 2000.0, "category": "Books", "image": "https://images.unsplash.com/photo-1589829085413-56de8ae18c73?w=400"}
    ]
    
    matching = [i for i in _curated_items if category_label.lower() in i["category"].lower() or i["category"].lower() in category_label.lower()]
    if not matching:
        matching = _curated_items
        
    products = []
    for i in range(20):
        item = matching[i % len(matching)]
        variant_name = item["name"] if i < len(matching) else f"{item['name']} - Edition {i//len(matching) + 1}"
        
        products.append({
            "id": 900000 + i,
            "name": variant_name,
            "price": item["price"] + (i * 0.1),
            "kes_price": item["kes_price"] + (i * 10),
            "client_kes": round((item["kes_price"] + (i * 10)) * 1.05, 2),
            "category": item["category"],
            "image": item["image"],
            "markup": 0.05,
            "source": "PSC Premium",
            "save_more": False
        })

    for product in products:
        product["id"] = _stable_product_id(
            product["name"], product["source"], product["category"], product["kes_price"]
        )
    return products


_INFLIGHT = {}

_SWR_INFLIGHT = set()
_SWR_INFLIGHT_LOCK = threading.Lock()


def _background_refresh_products(query, vendor=None, cache_key=None):
    if cache_key is None:
        cache_key = f"products::{vendor or 'all'}::{str(query).lower()}"

    with _SWR_INFLIGHT_LOCK:
        if cache_key in _SWR_INFLIGHT:
            return
        _SWR_INFLIGHT.add(cache_key)

    def _worker():
        if not _SCRAPE_LOCK.acquire(blocking=True, timeout=120):
            with _SWR_INFLIGHT_LOCK:
                _SWR_INFLIGHT.discard(cache_key)
            return
        try:
            fresh = _load_products_live(query, vendor=vendor)
            if fresh:
                _cache_set(cache_key, fresh)
                _register_products(fresh)
                meta = _DISK_CACHE_META.setdefault(cache_key, {})
                meta["refresh_count"] = int(meta.get("refresh_count", 0)) + 1
                meta["saved_at"] = time.time()
                _save_disk_cache(force=True)
                print(f"[PSC SWR] refreshed '{vendor or 'all'}:{query}' ({len(fresh)} products).")
        except Exception as e:
            print(f"[PSC SWR] refresh failed for '{query}': {e}")
        finally:
            _SCRAPE_LOCK.release()
            with _SWR_INFLIGHT_LOCK:
                _SWR_INFLIGHT.discard(cache_key)

    threading.Thread(target=_worker, daemon=True).start()



# === PSC PATCH: GOOGLE SHOPPING VENDOR-FILTERED AUGMENT ===
# When a user searches a keyword, we ALSO query Google Shopping and
# keep ONLY products whose seller/merchant matches one of the approved
# vendors already configured in this app. This gives a broad, live
# catalogue pulled straight from what our vendors have listed on Google
# without ever trusting an unknown seller.
# Set env PSC_GSHOP_ENABLED=0 to turn this off at runtime.

_PSC_GSHOP_ENABLED = os.getenv("PSC_GSHOP_ENABLED", "1").strip() == "1"

_VENDOR_GOOGLE_MATCH = {
    "jumia":          ["jumia"],
    "kilimall":       ["kilimall"],
    "carrefour":      ["carrefour", "maf carrefour"],
    "jiji":           ["jiji"],
    "fahavi":         ["fahavi", "fahavi computers"],
    "textbookcentre": ["text book centre", "textbookcentre"],
    "naivas":         ["naivas", "naivas supermarket"],
    "vivo":           ["vivo kenya", "vivo official store"],
    "copell":         ["copell"],
    "masoko":         ["masoko", "safaricom masoko"],
    "hotpoint":       ["hotpoint", "hotpoint appliances"],
    "samsungstore":   ["samsung brand store", "samsung experience store"],
}

_VENDOR_DOMAINS = {
    "jumia":          "jumia.co.ke",
    "kilimall":       "kilimall.co.ke",
    "carrefour":      "carrefour.ke",
    "jiji":           "jiji.co.ke",
    "fahavi":         "fahavicomputers.co.ke",
    "textbookcentre": "textbookcentre.com",
    "naivas":         "naivas.co.ke",
    "vivo":           "vivo.co.ke",
    "copell":         "copell.co.ke",
    "masoko":         "masoko.co.ke",
    "hotpoint":       "hotpoint.co.ke",
    "samsungstore":   "samsungbrandstore.co.ke",
}


def _gshop_match_vendor(card, card_text, page):
    # 1) Domain match in any anchor inside the card (strongest signal)
    try:
        for a in card.query_selector_all("a[href]"):
            href = (a.get_attribute("href") or "").lower()
            if not href: continue
            for vk, dom in _VENDOR_DOMAINS.items():
                if dom in href:
                    return vk
    except Exception:
        pass
    # 2) Known seller / merchant DOM selectors
    seller_txt = ""
    for sel in (".aULzUe", ".IuHnof", "[class*='merchant']",
                "[class*='seller']", "[aria-label*='seller']",
                "[aria-label*='store']", "[aria-label*='shop']"):
        try:
            el = card.query_selector(sel)
            if el: seller_txt += " " + (el.inner_text() or "")
        except Exception:
            continue
    hay = (seller_txt + " " + (card_text or "")).lower()
    # 3) Alias match on combined seller text + full card text
    for vk, aliases in _VENDOR_GOOGLE_MATCH.items():
        for alias in aliases:
            if alias in hay:
                return vk
    return None


def _gshop_human_scroll_and_clicks(page):
    import random as _rnd
    try:
        page.mouse.move(_rnd.randint(80, 480), _rnd.randint(80, 480))
        page.wait_for_timeout(_rnd.randint(250, 600))
        page.evaluate("window.scrollTo(0, document.body.scrollHeight / 3)")
        page.wait_for_timeout(_rnd.randint(900, 1500))
        page.evaluate("window.scrollTo(0, document.body.scrollHeight / 1.6)")
        page.wait_for_timeout(_rnd.randint(900, 1500))
    except Exception:
        pass
    # Try to activate "Seller"/"Shops" filter to reveal merchants cleanly
    for sel in ("div[role='button']:has-text('Seller')",
                "div[role='button']:has-text('Shops')",
                "button:has-text('Seller')",
                "button:has-text('Shops')"):
        try:
            btn = page.query_selector(sel)
            if btn and btn.is_visible():
                try:
                    btn.hover(); page.wait_for_timeout(400)
                except Exception: pass
                try:
                    btn.click(timeout=2000)
                    page.wait_for_timeout(1200)
                except Exception: pass
                break
        except Exception:
            continue


def _scrape_google_shopping_vendor_filtered(q, headers):
    """Google Shopping scrape, but ONLY keeps products whose seller
    matches one of our approved vendors. Uses human-like mouse + scroll
    + clicks so Google renders merchant info cleanly."""
    try:
        from playwright.sync_api import sync_playwright
        import random as _rnd
        products = []
        seen_names = set()

        with sync_playwright() as p:
            browser = _launch_browser(p)
            try:
                context = browser.new_context(
                    user_agent=headers.get("User-Agent") or _random_ua(),
                    viewport={"width": 1440, "height": 1000},
                    locale="en-KE", timezone_id="Africa/Nairobi",
                    extra_http_headers={
                        "Accept-Language": "en-KE,en-US;q=0.9,en;q=0.8",
                    },
                )
                page = context.new_page()
                try: page.add_init_script(_STEALTH_INIT_JS)
                except Exception: pass

                url = ("https://www.google.com/search?tbm=shop&hl=en&gl=ke&q="
                       + quote_plus(str(q)))
                try:
                    page.goto(url, wait_until="domcontentloaded", timeout=25000)
                except Exception:
                    pass
                page.wait_for_timeout(_rnd.randint(2200, 4200))

                try: body_txt = (page.content() or "").lower()
                except Exception: body_txt = ""
                if ("unusual traffic" in body_txt
                        or "not a robot" in body_txt
                        or "captcha" in body_txt):
                    print("[PSC GSHOP] Google CAPTCHA/soft-block - skipping '"
                          + str(q) + "'.")
                    return []

                _gshop_human_scroll_and_clicks(page)

                try:
                    page.wait_for_selector(
                        ".sh-dgr__content, .sh-dgr__grid-result, [data-docid]",
                        timeout=25000)
                except Exception:
                    pass

                cards = (page.query_selector_all(".sh-dgr__content")
                         or page.query_selector_all(".sh-dgr__grid-result")
                         or page.query_selector_all("[data-docid]"))
                print("[PSC GSHOP] matched " + str(len(cards))
                      + " Google Shopping cards for '" + str(q) + "'")

                for i, card in enumerate(cards[:40], start=1):
                    try:
                        name_el = (card.query_selector("h3")
                                   or card.query_selector("[role='heading']")
                                   or card.query_selector(".tAxDx"))
                        name = name_el.inner_text().strip() if name_el else ""
                        if not name or name.lower() in seen_names:
                            continue

                        price_el = (card.query_selector("span.a8Pemb")
                                    or card.query_selector("[aria-label*='KSh']")
                                    or card.query_selector("[class*='price']"))
                        price_text = (price_el.inner_text().strip()
                                      if price_el else "")
                        cleaned = (price_text.replace("KSh","")
                                   .replace("KES","").replace("Ksh","")
                                   .replace("kes","").replace(",","")
                                   .strip())
                        token = ""
                        for ch in cleaned:
                            if ch.isdigit() or ch == ".": token += ch
                            elif token: break
                        try: kes_price = float(token)
                        except ValueError: continue
                        if kes_price < 1: continue

                        img_el = card.query_selector("img")
                        img_url = ""
                        if img_el:
                            img_url = (img_el.get_attribute("src")
                                       or img_el.get_attribute("data-src") or "")
                            if img_url.startswith("//"):
                                img_url = "https:" + img_url

                        try: card_text = (card.inner_text() or "").lower()
                        except Exception: card_text = ""

                        matched_vendor = _gshop_match_vendor(card, card_text, page)
                        if not matched_vendor:
                            continue

                        seen_names.add(name.lower())
                        category = "Google Shopping"
                        am = markup_for(name, category)
                        products.append({
                            "id": i, "name": name,
                            "price": round((kes_price / PSC_TO_KES_RATE) * (1 + am), 2),
                            "kes_price": kes_price,
                            "client_kes": round(kes_price * (1 + am), 2),
                            "category": category,
                            "description": name[:60],
                            "image": img_url, "markup": am,
                            "source": "Google Shopping",
                            "vendor": matched_vendor,
                        })
                    except Exception:
                        continue
            finally:
                try: browser.close()
                except Exception: pass

        if products:
            print("[PSC GSHOP] returned " + str(len(products))
                  + " vendor-matched products for '" + str(q) + "'")
            return products
        print("[PSC GSHOP] produced 0 vendor-matched products for '"
              + str(q) + "'")
    except Exception as e:
        print("[PSC GSHOP] error: " + str(e))
    return []
# === END PSC PATCH: GOOGLE SHOPPING VENDOR-FILTERED AUGMENT ===


def _load_products_live(query, vendor=None):
    query = str(query or "").strip()
    if not query:
        return []

    all_products = _scrape_vendors_sequential(query, vendor=vendor)

    _seller_items = _seller_items_for_query(query)
    if _seller_items:
        _converted = []
        for _si in _seller_items:
            _p = _build_seller_product(_si)
            if _p:
                _converted.append(_p)
        if _converted:
            all_products = _converted + (all_products or [])

    # === PSC PATCH: GOOGLE SHOPPING VENDOR-FILTERED AUGMENT ===
    try:
        if not vendor and _PSC_GSHOP_ENABLED:
            _hdr = {
                "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                               "AppleWebKit/537.36 (KHTML, like Gecko) "
                               "Chrome/140.0.0.0 Safari/537.36"),
                "Accept": ("text/html,application/xhtml+xml,"
                           "application/xml;q=0.9,*/*;q=0.8"),
                "Accept-Language": "en-US,en;q=0.9",
            }
            _gshop = _scrape_google_shopping_vendor_filtered(query, _hdr)
            if _gshop:
                _seen = set()
                for _p in (all_products or []):
                    _n = (_p.get("name") or "").strip().lower()[:60]
                    if _n: _seen.add(_n)
                _added = 0
                for _gp in _gshop:
                    _n = (_gp.get("name") or "").strip().lower()[:60]
                    if _n and _n not in _seen:
                        all_products.append(_gp)
                        _seen.add(_n); _added += 1
                print("[PSC GSHOP] merged " + str(_added)
                      + " Google-Shopping vendor results for '"
                      + str(query) + "'")
    except Exception as _gse:
        print("[PSC GSHOP] augment failed: " + str(_gse))
    # === END PSC PATCH ===

    if not all_products:
        return []

    _register_products(all_products)
    return all_products


_USER_ACTIVITY_LOCK = threading.Lock()
_LAST_USER_ACTIVITY = 0.0


def _mark_user_activity():
    global _LAST_USER_ACTIVITY
    with _USER_ACTIVITY_LOCK:
        _LAST_USER_ACTIVITY = time.time()


def _recent_user_activity(within_seconds=15):
    with _USER_ACTIVITY_LOCK:
        return (time.time() - _LAST_USER_ACTIVITY) < within_seconds


def load_products(query, allow_block=True, vendor=None):
    try:
        from flask import has_request_context
        if has_request_context():
            _mark_user_activity()
    except Exception:
        pass

    query = str(query or "").strip()
    vendor = str(vendor or "").strip().lower() or None

    if not query:
        return []

    cache_key = f"products::{vendor or 'all'}::{query.lower()}"
    query_key = f"{vendor or 'all'}::{query.lower()}"

    # _PSC_SAFE_FAST_BOOT applied
    if os.environ.get("RENDER") and _cache_get_soft(cache_key) is None and not _scrape_recently_done(query_key):
        print(f"[PSC SAFE-FAST-BOOT] Cache empty for '{query}'. Returning fallback and backgrounding...")
        _background_refresh_products(query, vendor=vendor, cache_key=cache_key)
        return _fallback_products(query)

    cached = _cache_get(cache_key)
    if cached is not None:
        _register_products(cached)
        return cached

    stale = _cache_get_soft(cache_key)
    if stale is not None:
        print(f"[PSC SWR] serving stale for '{vendor or 'all'}:{query}' "
              f"and refreshing in background.")
        _register_products(stale)
        _background_refresh_products(query, vendor=vendor, cache_key=cache_key)
        return stale

    if _scrape_recently_done(query_key):
        print(f"[PSC SEARCH] '{vendor or 'all'}:{query}' in cooldown, returning empty.")
        return []

    acquired = _SCRAPE_LOCK.acquire(blocking=True, timeout=60)
    if not acquired:
        cached = _cache_get_soft(cache_key)
        if cached is not None:
            _register_products(cached)
            return cached
        print(f"[PSC SEARCH] Lock busy for '{vendor or 'all'}:{query}'; returning empty.")
        return []

    try:
        cached = _cache_get(cache_key)
        if cached is not None:
            _register_products(cached)
            return cached

        if _scrape_recently_done(query_key):
            print(f"[PSC SEARCH] '{vendor or 'all'}:{query}' in cooldown after wait, returning empty.")
            return []

        all_products = _load_products_live(query, vendor=vendor)

        _mark_scrape_done(query_key)

        if all_products:
            _register_products(all_products)
            _cache_set(cache_key, all_products)
            meta = _DISK_CACHE_META.setdefault(cache_key, {})
            meta["refresh_count"] = int(meta.get("refresh_count", 0)) + 1
            meta["saved_at"] = time.time()
            _cache_save_async()
            print(f"[PSC SEARCH] '{vendor or 'all'}:{query}' returned {len(all_products)} real products.")
            return all_products

        print(f"[PSC SEARCH] No real products found for '{vendor or 'all'}:{query}'.")
        return []

    finally:
        _SCRAPE_LOCK.release()


def load_products_multi(keywords, per_query=50, allow_block=True, vendor=None):
    combined = []
    seen_ids = set()
    seen_names = set()

    for kw in keywords:
        try:
            results = load_products(kw, allow_block=allow_block, vendor=vendor) or []
        except Exception as exc:
            print(f"[PSC MULTI] load_products('{kw}') failed: {exc}")
            results = []

        taken = 0
        for p in results:
            if per_query and taken >= per_query:
                break
            pid = p.get("id")
            pname = (p.get("name") or "").strip().lower()[:60]
            if pid in seen_ids or (pname and pname in seen_names):
                continue
            seen_ids.add(pid)
            if pname:
                seen_names.add(pname)
            combined.append(p)
            taken += 1

    print(f"[PSC MULTI] merged {len(combined)} products from {len(keywords)} keywords (vendor={vendor or 'all'})")
    return combined


_NEW_2026_KEYWORDS = [
    "iphone 18", "iphone18", "galaxy s26", "galaxy s25 ultra",
    "galaxy z fold 7", "galaxy z flip 7", "pixel 10", "pixel 10 pro",
    "redmi 15", "redmi note 15", "redmi turbo 5", "tecno camon 30",
    "tecno spark 30", "tecno phantom v fold 2", "infinix hot 50",
    "infinix note 50", "infinix zero 40", "oppo reno 13", "oppo find x8",
    "vivo v50", "vivo x200", "oneplus 13", "oneplus 14",
    "huawei nova 13", "huawei p70", "xiaomi 15", "xiaomi 15 ultra",
    "nokia g60", "nokia xr21", "macbook pro m5", "macbook air m4",
    "dell xps 15", "dell xps 16", "hp spectre x360 2026",
    "hp omen 16 2026", "lenovo thinkpad x1 carbon gen 13",
    "lenovo yoga 9i 2026", "asus zenbook 15 2026", "asus rog strix 2026",
    "acer swift go 16 2026", "acer predator 2026", "samsung neo qled 2026",
    "lg oled evo 2026", "sony bravia 9", "tcl qled 2026",
    "hisense u8n 2026", "airpods pro 3", "airpods 4", "galaxy buds 4",
    "galaxy buds 4 pro", "sony wh-1000xm6", "sony wf-1000xm6",
    "jbl tour one m3", "jbl tune 780nc", "apple watch series 11",
    "apple watch ultra 3", "galaxy watch 8", "galaxy watch ultra 2",
    "garmin fenix 9", "garmin venu 4", "playstation 6", "ps6",
    "xbox series z", "nintendo switch 2", "steam deck oled 2",
    "dyson v16", "dyson airwrap 2026", "samsung bespoke 2026",
    "lg washer 2026",
]


def _is_genuinely_new(product_name):
    name = product_name.lower()
    return any(kw in name for kw in _NEW_2026_KEYWORDS)


def _tag_new(products):
    for p in products:
        p["is_new"] = _is_genuinely_new(p["name"])
    random.shuffle(products)
    return products


def _get_shuffled_categories():
    import random
    shuffled = []
    for cat in CATEGORY_GROUPS:
        new_cat = cat.copy()
        # Try to find a real product image from the cache for this category
        products = _cache_get(f"products::all::{cat['query'].lower()}") or []
        if not products:
            products = _cache_get_soft(f"products::all::{cat['query'].lower()}") or []
        
        valid_images = [p.get("image") for p in products if p.get("image")]
        if valid_images:
            new_cat["image"] = random.choice(valid_images)
        # If no cached products, it safely falls back to the Unsplash image already in the dict
        shuffled.append(new_cat)
    return shuffled

def _build_hero(products, limit=10):
    with_img = [p for p in products if p.get("image")]
    random.shuffle(with_img)
    return with_img[:limit]


def _midnight_bonus_loop():
    while True:
        now = datetime.now()
        tomorrow = (now + timedelta(days=1)).replace(
            hour=0, minute=0, second=0, microsecond=0
        )
        wait_seconds = (tomorrow - now).total_seconds()
        try:
            time.sleep(wait_seconds)
        except Exception:
            time.sleep(60)
            continue

        try:
            _ensure_wallet_dir()
            granted = 0
            today = datetime.now().strftime("%Y-%m-%d")

            for fname in os.listdir(WALLET_DIR):
                if not fname.endswith(".json"):
                    continue
                try:
                    with open(os.path.join(WALLET_DIR, fname), "r", encoding="utf-8") as f:
                        wallet = json.load(f)
                except Exception:
                    continue

                address = wallet.get("address")
                if not address:
                    continue

                wallet = _ensure_wallet_structure(wallet)
                if wallet.get("last_login_bonus_date") == today:
                    continue

                wallet["daily_login_bonus_psc"] = round(
                    float(wallet.get("daily_login_bonus_psc", 0) or 0) + DAILY_LOGIN_BONUS_PSC, 2
                )
                wallet["last_login_bonus_date"] = today
                wallet["balance"] = _wallet_total(wallet)
                _save_wallet(wallet)
                _admin_merge_wallet(
                    address=address,
                    purchased_psc=wallet.get("wallet_psc", 0),
                    bonus_psc=wallet.get("bonus_psc", 0),
                    savings_psc=wallet.get("savings_psc", 0),
                    deposit_psc=wallet.get("deposit_psc", 0),
                )
                granted += 1

            print(f"[PSC] Midnight bonus granted to {granted} wallet(s).")
        except Exception as e:
            print(f"[PSC] Midnight bonus error: {e}")


# ============================================================
# WITHDRAWALS / PAYOUTS â€” ADMIN MANUAL ONLY (gateways removed)
# ============================================================

PSC_ADMIN_TOKEN       = os.getenv("PSC_ADMIN_TOKEN", "")
PAYOUT_MAX_KES        = float(os.getenv("PAYOUT_MAX_KES", "500") or 500)
PAYOUT_DAILY_MAX_KES  = float(os.getenv("PAYOUT_DAILY_MAX_KES", "5000") or 5000)


def _jload(path, default):
    try:
        if not os.path.exists(path):
            return default
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def _jsave(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

    last_err = None
    for _ in range(10):
        try:
            os.replace(tmp, path)
            return
        except (PermissionError, OSError) as e:
            last_err = e
            time.sleep(0.1)

    raise last_err if last_err else RuntimeError(f"Could not save {path}")


def _now():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _wq_all():
    d = _jload(WITHDRAWAL_QUEUE_FILE, [])
    return d if isinstance(d, list) else []


def _wq_find(wid):
    for row in _wq_all():
        if row.get("withdrawal_id") == wid:
            return row
    return None


def _wq_add(row):
    rows = _wq_all(); rows.append(row); _jsave(WITHDRAWAL_QUEUE_FILE, rows)


def _wq_update(wid, **fields):
    rows = _wq_all()
    for row in rows:
        if row.get("withdrawal_id") == wid:
            row.update(fields); _jsave(WITHDRAWAL_QUEUE_FILE, rows); return row
    return None


def _audit_add(row):
    rows = _jload(PAYOUT_AUDIT_FILE, [])
    if not isinstance(rows, list):
        rows = []
    rows.append(row)
    _jsave(PAYOUT_AUDIT_FILE, rows)


def _wallet_hold_withdrawal(address, amount_psc, withdrawal_id, source="wallet"):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found", None
    amt = round(float(amount_psc), 2)

    _src = str(source or "wallet").strip().lower()
    if _src not in ("wallet", "savings", "deposit"):
        _src = "wallet"
    _pocket_key   = {"wallet": "wallet_psc",
                     "savings": "savings_psc",
                     "deposit": "deposit_psc"}[_src]
    _pocket_label = {"wallet": "Spendable",
                     "savings": "Savings",
                     "deposit": "Deposit"}[_src]

    available = round(float(wallet.get(_pocket_key, 0) or 0), 2)
    if available - amt < 1.00 - 1e-9:
        return False, (f"Insufficient {_pocket_label} balance. Available "
                       f"{available:.2f} PSC. At least 1.00 PSC must remain "
                       f"in that pocket."), wallet
    wallet[_pocket_key] = round(available - amt, 2)
    wallet.setdefault("held_psc", 0.0)
    wallet["held_psc"] = round(float(wallet.get("held_psc", 0) or 0) + amt, 2)
    wallet.setdefault("withdrawals", [])
    wallet["withdrawals"].append({
        "withdrawal_id": withdrawal_id, "amount_psc": amt,
        "source": _src,
        "status": "PENDING", "created_at": _now(),
    })
    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True, "OK", wallet


def _wallet_release_or_settle(address, amount_psc, withdrawal_id, outcome):
    wallet = get_wallet(address)
    if not wallet:
        return False
    amt = round(float(amount_psc), 2)
    wallet["held_psc"] = round(max(0.0, float(wallet.get("held_psc", 0) or 0) - amt), 2)
    for w in wallet.get("withdrawals", []):
        if w.get("withdrawal_id") == withdrawal_id:
            _src = str(w.get("source") or "wallet").strip().lower()
            if _src not in ("wallet", "savings", "deposit"):
                _src = "wallet"
            if outcome == "REJECTED":
                _pk = {"wallet": "wallet_psc",
                       "savings": "savings_psc",
                       "deposit": "deposit_psc"}[_src]
                wallet[_pk] = round(float(wallet.get(_pk, 0) or 0) + amt, 2)
            w["status"] = outcome
            w["settled_at"] = _now()
            break
    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=address,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True


def _client_by_wallet(address):
    clients = _load_clients()
    for _k, c in clients.items():
        if str(c.get("wallet_address", "")).strip() == str(address).strip():
            return c
    return None


@app.route("/api/psc/withdraw/request", methods=["POST"])
def api_psc_withdraw_request():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        address = str(data.get("wallet") or session_wallet or "").strip()
        amount_psc = round(float(data.get("amount_psc") or 0), 2)
        method = str(data.get("method") or "mpesa").strip().lower()
        destination = str(data.get("destination") or "").strip()
        bank_code = str(data.get("bank_code") or "").strip()
        account_name = str(data.get("account_name") or "").strip()

        if not address:
            return jsonify({"success": False, "message": "wallet is required"}), 400
        if session_wallet and address != session_wallet:
            return jsonify({"success": False, "message": "Wallet does not match the logged-in account."}), 403
        if amount_psc < 1:
            return jsonify({"success": False, "message": "Minimum withdrawal is 1 PSC."}), 400

        verified_phone = session.get("verified_phone", "")
        verified_wallet = session.get("verified_wallet", "")
        if not verified_phone or not verified_wallet:
            return jsonify({"success": False,
                            "message": "Please verify your phone at checkout before withdrawing."}), 403
        if str(verified_wallet).strip() != address:
            return jsonify({"success": False, "message": "Session wallet mismatch."}), 403

        client = _client_by_wallet(address)
        if not client:
            return jsonify({"success": False, "message": "This wallet is not linked to a registered client."}), 404
        if _normalize_phone(client.get("phone", "")) != _normalize_phone(verified_phone):
            return jsonify({"success": False,
                            "message": "This wallet does not belong to your verified phone number."}), 403

        wallet = get_wallet(address)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"}), 404

        available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
        if amount_psc > available - 1.00 + 1e-9:
            return jsonify({
                "success": False,
                "message": (f"At least 1.00 PSC must remain in your account. "
                            f"Available: {available:.2f} PSC. "
                            f"Maximum withdrawable: {max(0.0, available - 1.00):.2f} PSC."),
                "wallet_psc": available,
                "max_withdrawable_psc": round(max(0.0, available - 1.00), 2),
                "psc_to_kes_rate": PSC_TO_KES_RATE,
            }), 400

        if method not in ("mpesa", "card-refund", "bank"):
            return jsonify({"success": False, "message": "method must be mpesa, card-refund or bank."}), 400

        amount_kes = round(amount_psc * PSC_TO_KES_RATE, 2)
        if amount_kes > PAYOUT_MAX_KES + 1e-9:
            return jsonify({
                "success": False,
                "message": (f"Single withdrawal limit is KES {PAYOUT_MAX_KES:.2f}. "
                            f"Please request a smaller amount."),
                "payout_max_kes": PAYOUT_MAX_KES,
            }), 400

        if method == "mpesa":
            dest = _normalize_phone(client.get("phone", "")) or destination
            if not dest:
                return jsonify({"success": False, "message": "No M-PESA number on this account."}), 400
        elif method == "card-refund":
            dest = destination or "manual-refund"
        else:
            if not bank_code or not destination:
                return jsonify({"success": False, "message": "bank_code and account number required."}), 400
            dest = destination

        _gate = _va_gate_payout(address, client, amount_kes,
                                method=method, destination=dest,
                                bank_code=bank_code)
        if not _gate.get("ok"):
            return jsonify({
                "success": False,
                "message": _gate.get("message", "Payout blocked by compliance gate."),
                "gate": _gate.get("gate"),
                "details": _gate.get("details", {}),
            }), _gate.get("status", 403)

        withdrawal_id = "WR-" + uuid.uuid4().hex[:12]

        ok, msg, _wallet = _wallet_hold_withdrawal(address, amount_psc, withdrawal_id)
        if not ok:
            return jsonify({"success": False, "message": msg}), 400

        _wq_add({
            "withdrawal_id": withdrawal_id,
            "wallet_address": address,
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "method": method,
            "destination": dest,
            "bank_code": bank_code,
            "account_name": account_name,
            "status": "PENDING",
            "created_at": _now(),
        })

        _admin_ledger_add({
            "type": "WITHDRAWAL_REQUEST",
            "withdrawal_id": withdrawal_id,
            "wallet_address": address,
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "mpesa_number": dest if method == "mpesa" else "",
            "method": method,
            "status": "PENDING",
            "time": _now(),
        })

        return jsonify({
            "success": True,
            "withdrawal_id": withdrawal_id,
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "method": method,
            "status": "PENDING",
            "message": (f"Withdrawal {withdrawal_id} created for KES {amount_kes:.2f}. "
                        f"Waiting for admin to review and pay manually."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/psc/withdraw/status/<wid>")
def api_psc_withdraw_status(wid):
    row = _wq_find(wid)
    if not row:
        return jsonify({"success": False, "message": "not found"}), 404
    return jsonify({"success": True, "withdrawal": row})


@app.route("/api/psc/withdraw/history/<address>")
def api_psc_withdraw_history(address):
    rows = [r for r in _wq_all() if r.get("wallet_address") == address]
    return jsonify({"success": True, "withdrawals": rows})


def _payout_today_total():
    today = datetime.now().strftime("%Y-%m-%d")
    total = 0.0
    for row in _jload(PAYOUT_AUDIT_FILE, []) or []:
        if str(row.get("at", "")).startswith(today) and row.get("result") == "SUCCESS":
            total += float(row.get("amount_kes") or 0)
    return round(total, 2)


def _ledger_update(withdrawal_id, **fields):
    rows = _jload(ADMIN_LEDGER_FILE, [])
    if not isinstance(rows, list):
        rows = []
    for row in rows:
        if row.get("withdrawal_id") == withdrawal_id:
            row.update(fields)
            _jsave(ADMIN_LEDGER_FILE, rows)
            return row
    return None


def _close_partial_if_any(wallet_address):
    try:
        rows = _jload(ADMIN_LEDGER_FILE, [])
        if not isinstance(rows, list):
            return None
        target = None
        for row in rows:
            if (row.get("type") == "PARTIAL_CHECKOUT_PAYMENT"
                    and row.get("wallet_address") == wallet_address
                    and row.get("status") == "AWAITING_TOPUP"):
                target = row
        if target is None:
            return None
        target["status"] = "TOPUP_RECEIVED"
        target["closed_at"] = _now()
        _jsave(ADMIN_LEDGER_FILE, rows)
        return target
    except Exception as e:
        print(f"[PARTIAL-CLOSE] failed: {e}")
        return None


@app.route("/api/admin/psc_payout_mark_paid", methods=["POST"])
def api_admin_psc_payout_mark_paid():
    try:
        sent = request.headers.get("X-PSC-Admin-Token", "")
        if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
            return jsonify({"success": False, "message": "forbidden"}), 403

        data = request.get_json() or {}
        wid = str(data.get("withdrawal_id") or "").strip()
        manual_code = str(data.get("mpesa_code") or "").strip()
        action = str(data.get("action") or "PAID").strip().upper()

        if not wid:
            return jsonify({"success": False, "message": "withdrawal_id required"}), 400

        row = _wq_find(wid)
        if not row:
            return jsonify({"success": False, "message": "withdrawal not found"}), 404
        if row.get("status") in ("PAID", "REJECTED"):
            return jsonify({"success": True, "withdrawal": row,
                            "message": f"Already {row.get('status')}"}), 200

        if action == "REJECTED":
            _wallet_release_or_settle(row["wallet_address"], float(row["amount_psc"]),
                                      wid, "REJECTED")
            _wq_update(wid, status="REJECTED", settled_at=_now(),
                       admin_note=str(data.get("note") or "").strip())
            _ledger_update(wid, status="REJECTED", settled_at=_now(),
                           admin_note=str(data.get("note") or "").strip())
            return jsonify({"success": True, "withdrawal": _wq_find(wid),
                            "message": "Withdrawal rejected and PSC returned to client."})

        amount_kes = float(row.get("amount_kes") or 0)

        if amount_kes > PAYOUT_MAX_KES + 1e-9:
            return jsonify({"success": False,
                            "message": f"Above per-transaction cap KES {PAYOUT_MAX_KES:.2f}"}), 400

        if _payout_today_total() + amount_kes > PAYOUT_DAILY_MAX_KES + 1e-9:
            return jsonify({"success": False,
                            "message": f"Would exceed today's KES {PAYOUT_DAILY_MAX_KES:.2f} payout cap"}), 400

        _client_obj = _client_by_wallet(row.get("wallet_address", "")) or {}
        _gate = _va_gate_payout(row.get("wallet_address", ""), _client_obj,
                                amount_kes,
                                method=row.get("method"),
                                destination=row.get("destination"),
                                bank_code=row.get("bank_code"),
                                admin_side=True)
        if not _gate.get("ok"):
            return jsonify({
                "success": False,
                "message": _gate.get("message", "Payout blocked by compliance gate."),
                "gate": _gate.get("gate"),
                "details": _gate.get("details", {}),
            }), _gate.get("status", 403)

        # Payment gateways removed: ALL payouts are now recorded as manual.
        _wq_update(wid, status="PAID", settled_at=_now(),
                   mpesa_code=manual_code, mode="manual")
        _wallet_release_or_settle(row["wallet_address"], float(row["amount_psc"]), wid, "PAID")
        _ledger_update(wid, status="PAID", settled_at=_now(),
                       mpesa_code=manual_code, mode="manual")
        _audit_add({"withdrawal_id": wid, "amount_kes": amount_kes, "method": row.get("method"),
                    "at": _now(), "mode": "manual", "result": "SUCCESS",
                    "mpesa_code": manual_code})
        _record_payout_velocity(row["wallet_address"], amount_kes, "MANUAL_PAID")
        _maybe_cbk_report(row, amount_kes)
        return jsonify({"success": True, "withdrawal": _wq_find(wid),
                        "message": "Recorded as manually paid."})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# KYC + PAYOUT COMPLIANCE (no gateways)
# ============================================================

KYC_REQUIRED             = os.getenv("KYC_REQUIRED", "1").strip() == "1"
KYC_ALLOWED_ID_TYPES     = [x.strip().lower() for x in
                            os.getenv("KYC_ALLOWED_ID_TYPES",
                                      "national_id,passport,drivers_license,huduma_namba,bvn,nin").split(",")
                            if x.strip()]
KYC_MIN_AGE              = int(os.getenv("KYC_MIN_AGE", "18") or 18)

PAYOUT_VELOCITY_MAX_PER_WEEK = int(os.getenv("PAYOUT_VELOCITY_MAX_PER_WEEK", "10") or 10)
PAYOUT_VELOCITY_MAX_PER_DAY  = int(os.getenv("PAYOUT_VELOCITY_MAX_PER_DAY", "3") or 3)

CBK_REPORT_THRESHOLD_KES = float(os.getenv("CBK_REPORT_THRESHOLD_KES", "1000000") or 1000000)
KRA_WHT_THRESHOLD_KES    = float(os.getenv("KRA_WHT_THRESHOLD_KES", "24000") or 24000)

VA_DIR = os.path.dirname(CLIENTS_FILE) or "."
KYC_FILE             = os.path.join(VA_DIR, "kyc_records.json")
COMPLIANCE_FILE      = os.path.join(VA_DIR, "compliance_flags.json")
VELOCITY_FILE        = os.path.join(VA_DIR, "payout_velocity.json")
CBK_REPORT_FILE      = os.path.join(VA_DIR, "cbk_reports.json")
SANCTIONS_FILE       = os.path.join(VA_DIR, "sanctions_blocklist.txt")

_SANCTIONS_INLINE = set(
    x.strip().lower() for x in
    os.getenv("SANCTIONS_BLOCKLIST", "").split(",") if x.strip()
)

_VA_LOCK = threading.Lock()


def _va_load(path, default):
    return _jload(path, default)


def _va_write(path, data):
    _jsave(path, data)


def _kyc_all():
    d = _va_load(KYC_FILE, {})
    return d if isinstance(d, dict) else {}


def _kyc_save(d):
    _va_write(KYC_FILE, d)


def _kyc_get(wallet_addr):
    return _kyc_all().get(wallet_addr)


def _kyc_upsert(wallet_addr, record):
    d = _kyc_all()
    d[wallet_addr] = record
    _kyc_save(d)


def _kyc_age_from_dob(dob_str):
    try:
        dob = datetime.strptime(str(dob_str).strip(), "%Y-%m-%d")
    except Exception:
        return None
    today = datetime.now()
    years = today.year - dob.year - ((today.month, today.day) < (dob.month, dob.day))
    return years


def _compliance_flags_all():
    d = _va_load(COMPLIANCE_FILE, [])
    return d if isinstance(d, list) else []


def _compliance_flag_add(row):
    rows = _compliance_flags_all()
    rows.append(row)
    _va_write(COMPLIANCE_FILE, rows)


def _sanctions_blocklist():
    names = set(_SANCTIONS_INLINE)
    try:
        if os.path.exists(SANCTIONS_FILE):
            with open(SANCTIONS_FILE, "r", encoding="utf-8") as f:
                for line in f:
                    s = line.strip().lower()
                    if s and not s.startswith("#"):
                        names.add(s)
    except Exception:
        pass
    return names


def _name_in_sanctions(name):
    n = str(name or "").strip().lower()
    if not n:
        return False
    for entry in _sanctions_blocklist():
        if entry and entry in n:
            return True
    return False


def _id_already_used(id_type, id_number, except_wallet=None):
    id_type = str(id_type or "").strip().lower()
    id_number = str(id_number or "").strip().lower()
    if not id_type or not id_number:
        return False
    for wallet, rec in _kyc_all().items():
        if except_wallet and wallet == except_wallet:
            continue
        if (str(rec.get("id_type", "")).strip().lower() == id_type and
                str(rec.get("id_number", "")).strip().lower() == id_number):
            return True
    return False


@app.route("/api/kyc/submit", methods=["POST"])
def api_kyc_submit():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()

        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        client = _client_by_wallet(wallet_addr)
        if not client:
            return jsonify({"success": False, "message": "Wallet not linked to any client."}), 404

        full_name   = str(data.get("full_name") or client.get("name") or "").strip()
        phone       = _normalize_phone(data.get("phone") or client.get("phone") or "")
        dob         = str(data.get("dob") or "").strip()
        id_type     = str(data.get("id_type") or "").strip().lower()
        id_number   = str(data.get("id_number") or "").strip()
        address     = str(data.get("address") or client.get("address") or "").strip()

        registered_phone = _normalize_phone(client.get("phone", ""))
        if registered_phone and phone and phone != registered_phone:
            return jsonify({
                "success": False,
                "status": "REJECTED_PHONE_MISMATCH",
                "message": ("The phone number you entered does not match the phone "
                            "on this account. Use the phone you registered with."),
            }), 400

        registered_name = str(client.get("name") or "").strip().lower()
        given_name      = str(full_name or "").strip().lower()
        if registered_name and given_name:
            reg_tokens   = {w for w in registered_name.split() if len(w) >= 3}
            given_tokens = {w for w in given_name.split()    if len(w) >= 3}
            if reg_tokens and not (reg_tokens & given_tokens):
                _compliance_flag_add({
                    "at": _now(), "wallet": wallet_addr,
                    "type": "KYC_NAME_MISMATCH",
                    "registered": registered_name,
                    "submitted":  given_name,
                })
                return jsonify({
                    "success": False,
                    "status": "REJECTED_NAME_MISMATCH",
                    "message": ("The name you entered does not match the name on "
                                "this account. Use the name you registered with."),
                }), 400

        errors = []
        if len(full_name) < 3:
            errors.append("full_name too short")
        if not phone or len(phone) < 9:
            errors.append("phone invalid")
        if not dob:
            errors.append("dob required")
        else:
            age = _kyc_age_from_dob(dob)
            if age is None:
                errors.append("dob must be YYYY-MM-DD")
            elif age < KYC_MIN_AGE:
                errors.append(f"must be at least {KYC_MIN_AGE} years old")
        if id_type not in KYC_ALLOWED_ID_TYPES:
            errors.append(f"id_type must be one of {KYC_ALLOWED_ID_TYPES}")
        if not id_number or len(id_number) < 5:
            errors.append("id_number invalid")

        if errors:
            return jsonify({"success": False, "message": "; ".join(errors)}), 400

        sanctions_hit = _name_in_sanctions(full_name)
        duplicate_id  = _id_already_used(id_type, id_number, except_wallet=wallet_addr)

        status = "VERIFIED"
        if sanctions_hit:
            status = "REJECTED_SANCTIONS"
            _compliance_flag_add({
                "at": _now(), "wallet": wallet_addr,
                "type": "SANCTIONS_HIT", "name": full_name,
                "detail": "KYC name matched blocklist",
            })
        elif duplicate_id:
            status = "REJECTED_DUPLICATE_ID"
            _compliance_flag_add({
                "at": _now(), "wallet": wallet_addr,
                "type": "DUPLICATE_ID",
                "detail": f"{id_type}:{id_number} already used",
            })

        record = {
            "wallet_address": wallet_addr,
            "full_name": full_name,
            "phone": phone,
            "dob": dob,
            "id_type": id_type,
            "id_number_masked": ("*" * max(0, len(id_number) - 4)) + id_number[-4:],
            "id_number_hash": hashlib.sha256(id_number.encode("utf-8")).hexdigest(),
            "id_number": id_number,
            "address": address,
            "status": status,
            "submitted_at": _now(),
            "reviewed_at": _now(),
        }
        _kyc_upsert(wallet_addr, record)
        _admin_ledger_add({
            "type": "KYC_SUBMIT",
            "wallet_address": wallet_addr,
            "status": status,
            "time": _now(),
        })

        return jsonify({
            "success": status == "VERIFIED",
            "status": status,
            "message": ("KYC verified." if status == "VERIFIED"
                        else f"KYC rejected: {status}"),
            "record": {
                "full_name": full_name, "status": status,
                "id_type": id_type, "id_number_masked": record["id_number_masked"],
            },
        }), (200 if status == "VERIFIED" else 400)
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/kyc/status", methods=["GET", "POST"])
def api_kyc_status():
    data = request.get_json(silent=True) or {}
    session_wallet = session.get("wallet", "")
    wallet_addr = str(data.get("wallet") or request.args.get("wallet") or session_wallet or "").strip()
    if not wallet_addr:
        return jsonify({"success": False, "message": "Wallet is required."}), 400
    rec = _kyc_get(wallet_addr)
    if not rec:
        return jsonify({"success": True, "kyc_status": "NOT_SUBMITTED"})
    return jsonify({
        "success": True,
        "kyc_status": rec.get("status", "UNKNOWN"),
        "full_name": rec.get("full_name", ""),
        "id_type": rec.get("id_type", ""),
        "id_number_masked": rec.get("id_number_masked", ""),
        "submitted_at": rec.get("submitted_at", ""),
    })


def _maybe_cbk_report(withdrawal_row, amount_kes):
    try:
        if amount_kes < KRA_WHT_THRESHOLD_KES:
            return
        row = {
            "at": _now(),
            "withdrawal_id": withdrawal_row.get("withdrawal_id"),
            "wallet_address": withdrawal_row.get("wallet_address"),
            "amount_kes": amount_kes,
            "above_cbk": amount_kes >= CBK_REPORT_THRESHOLD_KES,
            "above_kra_wht": amount_kes >= KRA_WHT_THRESHOLD_KES,
            "method": withdrawal_row.get("method"),
        }
        rows = _va_load(CBK_REPORT_FILE, [])
        if not isinstance(rows, list):
            rows = []
        rows.append(row)
        _va_write(CBK_REPORT_FILE, rows)
        if row["above_cbk"]:
            _compliance_flag_add({
                "at": _now(), "wallet": row["wallet_address"],
                "type": "CBK_THRESHOLD_PAYOUT",
                "amount_kes": amount_kes,
                "withdrawal_id": row["withdrawal_id"],
            })
    except Exception as e:
        print(f"[CBK] report failed: {e}")


def _velocity_all():
    d = _va_load(VELOCITY_FILE, {})
    return d if isinstance(d, dict) else {}


def _velocity_save(d):
    _va_write(VELOCITY_FILE, d)


def _velocity_stats(wallet_addr):
    today = datetime.now().strftime("%Y-%m-%d")
    week_ago = (datetime.now() - timedelta(days=7)).strftime("%Y-%m-%d")
    d = _velocity_all().get(wallet_addr) or {"events": []}
    events = d.get("events", [])
    today_count = sum(1 for e in events if str(e.get("at", "")).startswith(today))
    week_count = sum(1 for e in events if str(e.get("at", ""))[:10] >= week_ago)
    return {"today_count": today_count, "week_count": week_count, "events": events}


def _record_payout_velocity(wallet_addr, amount_kes, kind="PAID"):
    d = _velocity_all()
    entry = d.get(wallet_addr) or {"events": []}
    entry["events"].append({
        "at": _now(), "amount_kes": amount_kes, "kind": kind,
    })
    entry["events"] = entry["events"][-200:]
    d[wallet_addr] = entry
    _velocity_save(d)


def _velocity_check(wallet_addr):
    stats = _velocity_stats(wallet_addr)
    if stats["today_count"] + 1 > PAYOUT_VELOCITY_MAX_PER_DAY:
        return False, f"Daily payout limit reached ({PAYOUT_VELOCITY_MAX_PER_DAY})."
    if stats["week_count"] + 1 > PAYOUT_VELOCITY_MAX_PER_WEEK:
        return False, f"Weekly payout limit reached ({PAYOUT_VELOCITY_MAX_PER_WEEK})."
    return True, "OK"


@app.route("/api/admin/payout/velocity/<wallet_addr>", methods=["GET"])
def api_admin_payout_velocity(wallet_addr):
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({"success": False, "message": "forbidden"}), 403
    return jsonify({"success": True, "stats": _velocity_stats(wallet_addr)})


def _destination_sanctioned(destination, bank_code=""):
    dest = str(destination or "").strip()
    if not dest:
        return False
    target = dest.lower()
    for entry in _sanctions_blocklist():
        if entry and entry in target:
            return True
    return False


def _va_gate_payout(wallet_addr, client, amount_kes, method="", destination="",
                    bank_code="", admin_side=False):
    """Compliance gate for payouts. Payment gateways removed, so no
    external bank-account resolution is performed. The admin confirms
    destination manually."""
    try:
        vok, vmsg = _velocity_check(wallet_addr)
        if not vok:
            return {"ok": False, "status": 429, "gate": "velocity",
                    "message": vmsg,
                    "details": _velocity_stats(wallet_addr)}

        if _destination_sanctioned(destination, bank_code):
            _compliance_flag_add({
                "at": _now(), "wallet": wallet_addr,
                "type": "SANCTIONED_DESTINATION",
                "destination": destination, "bank_code": bank_code,
                "amount_kes": amount_kes, "method": method,
            })
            return {"ok": False, "status": 403, "gate": "sanctions_destination",
                    "message": "Destination matches sanctions blocklist."}

        if KYC_REQUIRED and amount_kes > 0:
            kyc = _kyc_get(wallet_addr)
            if not kyc or kyc.get("status") != "VERIFIED":
                if admin_side:
                    _compliance_flag_add({
                        "at": _now(), "wallet": wallet_addr,
                        "type": "PAYOUT_WITHOUT_KYC_ADMIN_OVERRIDE",
                        "amount_kes": amount_kes,
                    })
                else:
                    return {
                        "ok": False, "status": 403, "gate": "kyc_required",
                        "message": "Complete KYC before requesting a payout.",
                        "details": {"kyc_status": (kyc or {}).get("status", "NOT_SUBMITTED")},
                    }

        if amount_kes > PAYOUT_MAX_KES + 1e-9:
            return {"ok": False, "status": 400, "gate": "per_tx_cap",
                    "message": f"Above per-transaction cap KES {PAYOUT_MAX_KES:.2f}"}

        return {"ok": True}
    except Exception as e:
        print(f"[VA GATE] error: {e}")
        return {"ok": True}


@app.route("/api/admin/compliance/flags", methods=["GET"])
def api_admin_compliance_flags():
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({"success": False, "message": "forbidden"}), 403
    return jsonify({"success": True, "flags": _compliance_flags_all()})


@app.route("/api/admin/compliance/flag", methods=["POST"])
def api_admin_compliance_flag():
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({"success": False, "message": "forbidden"}), 403
    data = request.get_json() or {}
    _compliance_flag_add({
        "at": _now(),
        "wallet": str(data.get("wallet") or "").strip(),
        "type": str(data.get("type") or "MANUAL_FLAG"),
        "detail": str(data.get("detail") or ""),
        "by": "admin",
    })
    return jsonify({"success": True})


@app.route("/api/admin/cbk/report", methods=["GET"])
def api_admin_cbk_report():
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({"success": False, "message": "forbidden"}), 403
    return jsonify({"success": True, "reports": _va_load(CBK_REPORT_FILE, [])})


@app.route("/api/admin/aml/screen", methods=["POST"])
def api_admin_aml_screen():
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({"success": False, "message": "forbidden"}), 403
    data = request.get_json() or {}
    name = str(data.get("name") or "")
    wallet_addr = str(data.get("wallet") or "")
    hit = _name_in_sanctions(name)
    if hit:
        _compliance_flag_add({
            "at": _now(), "wallet": wallet_addr,
            "type": "AML_MANUAL_SANCTIONS_HIT", "name": name,
        })
    return jsonify({"success": True, "sanctions_hit": hit})


# ============================================================
# WALLET UPGRADE LAYER â€” P2P + HIGH-VALUE WITHDRAWALS
# ============================================================

WALLET_DEPOSIT_MAX_KES        = float(os.getenv("WALLET_DEPOSIT_MAX_KES", "0") or 0)
WALLET_WITHDRAW_DAILY_MAX_KES = float(os.getenv("WALLET_WITHDRAW_DAILY_MAX_KES", "100000") or 100000)
WALLET_TRANSFER_MIN_PSC       = float(os.getenv("WALLET_TRANSFER_MIN_PSC", "1") or 1)
WALLET_TRANSFER_MAX_PSC       = float(os.getenv("WALLET_TRANSFER_MAX_PSC", "0") or 0)
WALLET_TRANSFER_DAILY_MAX_PSC = float(os.getenv("WALLET_TRANSFER_DAILY_MAX_PSC", "0") or 0)
WALLET_CARD_DEPOSIT_ENABLED   = os.getenv("WALLET_CARD_DEPOSIT_ENABLED", "1").strip() == "1"
WALLET_BANK_DEPOSIT_ENABLED   = os.getenv("WALLET_BANK_DEPOSIT_ENABLED", "1").strip() == "1"
WALLET_MPESA_DEPOSIT_ENABLED  = os.getenv("WALLET_MPESA_DEPOSIT_ENABLED", "1").strip() == "1"

WALLET_OPS_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "wallet_ledger_ops.json"
)

_WALLET_OPS_LOCK = threading.Lock()


def _wallet_ops_all():
    d = _jload(WALLET_OPS_FILE, [])
    return d if isinstance(d, list) else []


def _wallet_ops_add(row):
    with _WALLET_OPS_LOCK:
        rows = _wallet_ops_all()
        rows.append(row)
        _jsave(WALLET_OPS_FILE, rows)


def _wallet_deposit_today_kes(wallet_addr):
    today = datetime.now().strftime("%Y-%m-%d")
    total = 0.0
    for r in _wallet_ops_all():
        if r.get("type") != "DEPOSIT":
            continue
        if r.get("wallet_address") != wallet_addr:
            continue
        if r.get("status") != "COMPLETED":
            continue
        if str(r.get("created_at", "")).startswith(today):
            total += float(r.get("amount_kes") or 0)
    return round(total, 2)


def _wallet_withdraw_today_kes(wallet_addr):
    today = datetime.now().strftime("%Y-%m-%d")
    seen = set()
    total = 0.0
    for r in _wallet_ops_all():
        if r.get("type") not in ("WITHDRAWAL_REQUEST", "WITHDRAWAL_PAID"):
            continue
        if r.get("wallet_address") != wallet_addr:
            continue
        if r.get("status") in ("REJECTED",):
            continue
        if not str(r.get("created_at", "")).startswith(today):
            continue
        wid = str(r.get("withdrawal_id") or r.get("request_id") or "")
        if wid and wid in seen:
            continue
        if wid:
            seen.add(wid)
        total += float(r.get("amount_kes") or 0)
    return round(total, 2)


def _wallet_transfer_today_psc(wallet_addr):
    today = datetime.now().strftime("%Y-%m-%d")
    total = 0.0
    for r in _wallet_ops_all():
        if r.get("type") != "TRANSFER_OUT":
            continue
        if r.get("wallet_address") != wallet_addr:
            continue
        if r.get("status") != "COMPLETED":
            continue
        if str(r.get("created_at", "")).startswith(today):
            total += float(r.get("amount_psc") or 0)
    return round(total, 2)


def _wallet_ui_deposit_options():
    # Payment gateways removed: no direct deposit channels available.
    # Deposits can only be made by admin manual credit or P2P incoming.
    return []


@app.route("/api/wallet/transfer/lookup", methods=["POST"])
def api_wallet_transfer_lookup():
    try:
        data = request.get_json() or {}
        query = str(data.get("query") or data.get("phone") or data.get("wallet") or "").strip()
        if not query:
            return jsonify({"success": False, "message": "query is required"}), 400

        client = None
        if query.upper().startswith("PSC") and len(query) >= 12:
            client = _client_by_wallet(query)
        else:
            client = get_client_by_phone(query)

        if not client:
            return jsonify({"success": False, "message": "Recipient not found."}), 404

        recipient_wallet = str(client.get("wallet_address", "")).strip()
        if not recipient_wallet:
            return jsonify({"success": False, "message": "Recipient has no wallet."}), 404

        return jsonify({
            "success": True,
            "recipient": {
                "name": client.get("name", ""),
                "phone": client.get("phone", ""),
                "wallet": recipient_wallet,
                "wallet_short": recipient_wallet[:10] + "â€¦" + recipient_wallet[-6:],
            },
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/transfer", methods=["POST"])
def api_wallet_transfer():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        sender_wallet = str(data.get("wallet") or session_wallet or "").strip()

        if not sender_wallet:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and sender_wallet != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        recipient_query = str(
            data.get("recipient")
            or data.get("recipient_phone")
            or data.get("recipient_wallet")
            or ""
        ).strip()
        if not recipient_query:
            return jsonify({"success": False, "message": "recipient is required"}), 400

        amount_psc = round(float(data.get("amount_psc") or 0), 2)
        if amount_psc < WALLET_TRANSFER_MIN_PSC:
            return jsonify({"success": False,
                            "message": f"Minimum transfer is {WALLET_TRANSFER_MIN_PSC} PSC."}), 400
        if WALLET_TRANSFER_MAX_PSC > 0 and amount_psc > WALLET_TRANSFER_MAX_PSC + 1e-9:
            return jsonify({"success": False,
                            "message": f"Single transfer exceeds {WALLET_TRANSFER_MAX_PSC} PSC."}), 400
        if WALLET_TRANSFER_DAILY_MAX_PSC > 0:
            used = _wallet_transfer_today_psc(sender_wallet)
            if used + amount_psc > WALLET_TRANSFER_DAILY_MAX_PSC + 1e-9:
                return jsonify({
                    "success": False,
                    "message": f"Daily transfer cap is {WALLET_TRANSFER_DAILY_MAX_PSC} PSC. Used {used:.2f}."}), 400

        if recipient_query.upper().startswith("PSC") and len(recipient_query) >= 12:
            recipient_client = _client_by_wallet(recipient_query)
        else:
            recipient_client = get_client_by_phone(recipient_query)

        if not recipient_client:
            return jsonify({"success": False, "message": "Recipient not found."}), 404

        recipient_wallet = str(recipient_client.get("wallet_address", "")).strip()
        if not recipient_wallet:
            return jsonify({"success": False, "message": "Recipient has no wallet."}), 404
        if recipient_wallet == sender_wallet:
            return jsonify({"success": False, "message": "Cannot transfer to yourself."}), 400

        sender_client = _client_by_wallet(sender_wallet) or {}

        sender_phone_in_session = session.get("verified_phone", "")
        if sender_phone_in_session:
            if _normalize_phone(sender_client.get("phone", "")) != _normalize_phone(sender_phone_in_session):
                return jsonify({"success": False, "message": "Sender verification failed."}), 403

        ok, msg = deduct_wallet_psc(sender_wallet, amount_psc)
        if not ok:
            return jsonify({"success": False, "message": msg}), 400

        cred_ok, cred_msg, _ = _add_purchased_psc(
            recipient_wallet, amount_psc,
            kes_amount=round(amount_psc * PSC_TO_KES_RATE, 2),
            payment_reference=f"P2P:{sender_wallet}",
        )
        if not cred_ok:
            try:
                _add_purchased_psc(
                    sender_wallet, amount_psc,
                    kes_amount=round(amount_psc * PSC_TO_KES_RATE, 2),
                    payment_reference="P2P_ROLLBACK",
                )
            except Exception:
                pass
            return jsonify({"success": False,
                            "message": f"Recipient credit failed: {cred_msg}"}), 500

        transfer_id = "TX-" + uuid.uuid4().hex[:12]
        _wallet_ops_add({
            "type": "TRANSFER_OUT",
            "transfer_id": transfer_id,
            "wallet_address": sender_wallet,
            "recipient_wallet": recipient_wallet,
            "recipient_name": recipient_client.get("name", ""),
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "status": "COMPLETED",
            "created_at": _now(),
        })
        _wallet_ops_add({
            "type": "TRANSFER_IN",
            "transfer_id": transfer_id,
            "wallet_address": recipient_wallet,
            "sender_wallet": sender_wallet,
            "sender_name": sender_client.get("name", ""),
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "status": "COMPLETED",
            "created_at": _now(),
        })

        _admin_ledger_add({
            "type": "P2P_TRANSFER",
            "transfer_id": transfer_id,
            "sender_wallet": sender_wallet,
            "recipient_wallet": recipient_wallet,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "status": "COMPLETED",
            "time": _now(),
        })

        sender_wallet_after = get_wallet(sender_wallet) or {}
        return jsonify({
            "success": True,
            "transfer_id": transfer_id,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "recipient": {
                "name": recipient_client.get("name", ""),
                "phone": recipient_client.get("phone", ""),
                "wallet": recipient_wallet,
            },
            "wallet_psc_after": round(float(sender_wallet_after.get("wallet_psc", 0) or 0), 2),
            "message": (f"Sent {amount_psc:.2f} PSC (KES {amount_psc * PSC_TO_KES_RATE:.2f}) "
                        f"to {recipient_client.get('name', 'recipient')}."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/transfer/history/<wallet_addr>", methods=["GET"])
def api_wallet_transfer_history(wallet_addr):
    rows = [r for r in _wallet_ops_all()
            if r.get("type") in ("TRANSFER_OUT", "TRANSFER_IN")
            and r.get("wallet_address") == wallet_addr]
    return jsonify({"success": True, "transfers": rows})


@app.route("/api/wallet/withdraw/highvalue", methods=["POST"])
def api_wallet_withdraw_highvalue():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()
        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        amount_psc = round(float(data.get("amount_psc") or 0), 2)
        if amount_psc < 1:
            return jsonify({"success": False, "message": "Minimum withdrawal is 1 PSC."}), 400

        method = str(data.get("method") or "mpesa").strip().lower()
        if method not in ("mpesa", "bank"):
            return jsonify({"success": False, "message": "method must be mpesa or bank."}), 400
        destination = str(data.get("destination") or "").strip()
        bank_code   = str(data.get("bank_code") or "").strip()

        client = _client_by_wallet(wallet_addr)
        if not client:
            return jsonify({"success": False, "message": "Wallet not linked to any client."}), 404

        if method == "mpesa":
            destination = _normalize_phone(destination) or _normalize_phone(client.get("phone", ""))
            if not destination:
                return jsonify({"success": False, "message": "No M-Pesa number on this account."}), 400
        else:
            if not destination or not bank_code:
                return jsonify({"success": False,
                                "message": "bank_code and destination are required."}), 400

        _source = str(data.get("source") or "wallet").strip().lower()
        if _source not in ("wallet", "savings", "deposit"):
            _source = "wallet"
        _pk = {"wallet": "wallet_psc",
               "savings": "savings_psc",
               "deposit": "deposit_psc"}[_source]
        _plabel = {"wallet": "Spendable",
                   "savings": "Savings",
                   "deposit": "Deposit"}[_source]
        available = round(float(wallet.get(_pk, 0) or 0), 2)
        if amount_psc > available - 1.00 + 1e-9:
            return jsonify({
                "success": False,
                "message": (f"At least 1.00 PSC must remain in your {_plabel} pocket. "
                            f"Available {available:.2f} PSC. "
                            f"Maximum withdrawable {max(0.0, available - 1.00):.2f} PSC."),
                "wallet_psc": available,
                "source": _source,
                "max_withdrawable_psc": round(max(0.0, available - 1.00), 2),
            }), 400

        amount_kes = round(amount_psc * PSC_TO_KES_RATE, 2)
        used_today = _wallet_withdraw_today_kes(wallet_addr)
        if used_today + amount_kes > WALLET_WITHDRAW_DAILY_MAX_KES + 1e-9:
            return jsonify({
                "success": False,
                "message": (f"Daily withdrawal cap is KES {WALLET_WITHDRAW_DAILY_MAX_KES:.2f}. "
                            f"Used today: KES {used_today:.2f}. Requested: KES {amount_kes:.2f}."),
                "daily_max_kes": WALLET_WITHDRAW_DAILY_MAX_KES,
                "used_today_kes": used_today,
                "remaining_today_kes": round(max(0.0, WALLET_WITHDRAW_DAILY_MAX_KES - used_today), 2),
            }), 400

        gate = _va_gate_payout(wallet_addr, client, amount_kes,
                               method=method, destination=destination,
                               bank_code=bank_code)
        if not gate.get("ok"):
            return jsonify({
                "success": False,
                "message": gate.get("message", "Payout blocked by compliance gate."),
                "gate": gate.get("gate"),
                "details": gate.get("details", {}),
            }), gate.get("status", 403)

        withdrawal_id = "WRV-" + uuid.uuid4().hex[:12]
        ok, msg, _w = _wallet_hold_withdrawal(wallet_addr, amount_psc, withdrawal_id, source=_source)
        if not ok:
            return jsonify({"success": False, "message": msg}), 400

        _wq_add({
            "withdrawal_id": withdrawal_id,
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "method": method,
            "destination": destination,
            "bank_code": bank_code,
            "source": _source,
            "status": "PENDING_ADMIN",
            "created_at": _now(),
        })
        _wallet_ops_add({
            "type": "WITHDRAWAL_REQUEST",
            "withdrawal_id": withdrawal_id,
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "method": method,
            "destination": destination,
            "source": _source,
            "status": "PENDING_ADMIN",
            "created_at": _now(),
        })
        _admin_ledger_add({
            "type": "WITHDRAWAL_REQUEST_HIGHVALUE",
            "withdrawal_id": withdrawal_id,
            "wallet_address": wallet_addr,
            "name": client.get("name", ""),
            "phone": client.get("phone", ""),
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "method": method,
            "destination": destination,
            "source": _source,
            "status": "PENDING_ADMIN",
            "time": _now(),
        })

        return jsonify({
            "success": True,
            "withdrawal_id": withdrawal_id,
            "status": "PENDING_ADMIN",
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "method": method,
            "source": _source,
            "daily_max_kes": WALLET_WITHDRAW_DAILY_MAX_KES,
            "used_today_kes": used_today + amount_kes,
            "message": (f"Withdrawal {withdrawal_id} created for KES {amount_kes:.2f}. "
                        f"Admin confirmation is required."),
            "ui": {
                "title": "Withdrawal Request",
                "status": "PENDING_ADMIN",
                "confirm_label": "Admin: Confirm & Pay",
            },
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/withdraw/daily-usage/<wallet_addr>", methods=["GET"])
def api_wallet_withdraw_daily_usage(wallet_addr):
    used = _wallet_withdraw_today_kes(wallet_addr)
    return jsonify({
        "success": True,
        "daily_max_kes": WALLET_WITHDRAW_DAILY_MAX_KES,
        "used_today_kes": used,
        "remaining_today_kes": round(max(0.0, WALLET_WITHDRAW_DAILY_MAX_KES - used), 2),
    })


@app.route("/api/admin/wallet/withdraw/confirm", methods=["POST"])
def api_admin_wallet_withdraw_confirm():
    try:
        sent = request.headers.get("X-PSC-Admin-Token", "")
        if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
            return jsonify({"success": False, "message": "forbidden"}), 403

        data = request.get_json() or {}
        wid = str(data.get("withdrawal_id") or "").strip()
        action = str(data.get("action") or "PAID").strip().upper()
        code = str(data.get("mpesa_code") or data.get("reference") or "").strip()

        if not wid:
            return jsonify({"success": False, "message": "withdrawal_id required"}), 400

        row = _wq_find(wid)
        if not row:
            return jsonify({"success": False, "message": "withdrawal not found"}), 404
        if row.get("status") in ("PAID", "REJECTED"):
            return jsonify({"success": True, "withdrawal": row,
                            "message": f"Already {row.get('status')}"}), 200

        amount_psc = float(row.get("amount_psc") or 0)
        amount_kes = float(row.get("amount_kes") or 0)
        wallet_addr = row.get("wallet_address")

        if action == "REJECTED":
            _wallet_release_or_settle(wallet_addr, amount_psc, wid, "REJECTED")
            _wq_update(wid, status="REJECTED", settled_at=_now(),
                       admin_note=str(data.get("note") or "").strip())
            _wallet_ops_add({
                "type": "WITHDRAWAL_PAID",
                "withdrawal_id": wid,
                "wallet_address": wallet_addr,
                "amount_psc": amount_psc,
                "amount_kes": amount_kes,
                "status": "REJECTED",
                "created_at": _now(),
            })
            return jsonify({"success": True, "withdrawal": _wq_find(wid),
                            "message": "Withdrawal rejected; funds returned."})

        # Payment gateways removed: ALL payouts are manual.
        _wq_update(wid, status="PAID", settled_at=_now(),
                   mpesa_code=code, mode="manual")

        _wallet_release_or_settle(wallet_addr, amount_psc, wid, "PAID")
        _ledger_update(wid, status="PAID", settled_at=_now(),
                       mode="manual", reference=code)
        _audit_add({
            "withdrawal_id": wid, "amount_kes": amount_kes,
            "method": row.get("method"),
            "at": _now(), "mode": "manual",
            "result": "SUCCESS", "reference": code,
        })
        _wallet_ops_add({
            "type": "WITHDRAWAL_PAID",
            "withdrawal_id": wid,
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "status": "COMPLETED",
            "created_at": _now(),
        })
        _record_payout_velocity(wallet_addr, amount_kes, "CONFIRMED")
        _maybe_cbk_report(row, amount_kes)

        return jsonify({"success": True, "withdrawal": _wq_find(wid),
                        "message": "Withdrawal confirmed and settled."})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# SAVINGS SUB-BALANCE
# ============================================================

WALLET_SAVINGS_ENABLED       = os.getenv("WALLET_SAVINGS_ENABLED", "1").strip() == "1"
WALLET_SAVINGS_MIN_MOVE_PSC  = float(os.getenv("WALLET_SAVINGS_MIN_MOVE_PSC", "0.01") or 0.01)
WALLET_SAVINGS_MIN_LEAVE_PSC = float(os.getenv("WALLET_SAVINGS_MIN_LEAVE_PSC", "1.00") or 1.00)

WALLET_SAVINGS_OPS_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "wallet_savings_ops.json"
)

_WALLET_SAVINGS_LOCK = threading.Lock()


def _savings_ops_all():
    d = _jload(WALLET_SAVINGS_OPS_FILE, [])
    return d if isinstance(d, list) else []


def _savings_ops_add(row):
    with _WALLET_SAVINGS_LOCK:
        rows = _savings_ops_all()
        rows.append(row)
        _jsave(WALLET_SAVINGS_OPS_FILE, rows)


def _savings_stats(wallet_addr):
    rows = [r for r in _savings_ops_all() if r.get("wallet_address") == wallet_addr]
    total_in = sum(float(r.get("amount_psc") or 0) for r in rows if r.get("direction") == "IN")
    total_out = sum(float(r.get("amount_psc") or 0) for r in rows if r.get("direction") == "OUT")
    return {
        "in_psc": round(total_in, 2),
        "out_psc": round(total_out, 2),
        "net_psc": round(total_in - total_out, 2),
        "events": len(rows),
    }


@app.route("/api/wallet/savings/<wallet_addr>", methods=["GET"])
def api_wallet_savings_get(wallet_addr):
    wallet = get_wallet(wallet_addr)
    if not wallet:
        return jsonify({"success": False, "message": "Wallet not found."}), 404
    return jsonify({
        "success": True,
        "wallet": wallet_addr,
        "savings_psc": round(float(wallet.get("savings_psc", 0) or 0), 2),
        "savings_value_kes": round(float(wallet.get("savings_psc", 0) or 0) * PSC_TO_KES_RATE, 2),
        "wallet_psc": round(float(wallet.get("wallet_psc", 0) or 0), 2),
        "deposit_psc": round(float(wallet.get("deposit_psc", 0) or 0), 2),
        "bonus_psc": round(float(wallet.get("bonus_psc", 0) or 0), 2),
        "history": [r for r in _savings_ops_all() if r.get("wallet_address") == wallet_addr],
        "stats": _savings_stats(wallet_addr),
        "psc_to_kes_rate": PSC_TO_KES_RATE,
        "enabled": WALLET_SAVINGS_ENABLED,
        "min_move_psc": WALLET_SAVINGS_MIN_MOVE_PSC,
        "min_leave_psc": WALLET_SAVINGS_MIN_LEAVE_PSC,
    })


@app.route("/api/wallet/savings/move_in", methods=["POST"])
def api_wallet_savings_move_in():
    if not WALLET_SAVINGS_ENABLED:
        return jsonify({"success": False,
                        "message": "Savings is disabled (WALLET_SAVINGS_ENABLED=0)."}), 503
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()
        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        amount_psc = round(float(data.get("amount_psc") or 0), 2)
        if amount_psc < WALLET_SAVINGS_MIN_MOVE_PSC:
            return jsonify({"success": False,
                            "message": f"Minimum move-in is {WALLET_SAVINGS_MIN_MOVE_PSC} PSC."}), 400

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
        if available - amount_psc < WALLET_SAVINGS_MIN_LEAVE_PSC - 1e-9:
            return jsonify({
                "success": False,
                "message": (f"At least {WALLET_SAVINGS_MIN_LEAVE_PSC:.2f} PSC must remain in your "
                            f"spendable balance. Available: {available:.2f} PSC. "
                            f"Maximum movable: {max(0.0, available - WALLET_SAVINGS_MIN_LEAVE_PSC):.2f} PSC."),
                "wallet_psc": available,
                "max_move_psc": round(max(0.0, available - WALLET_SAVINGS_MIN_LEAVE_PSC), 2),
            }), 400

        wallet["wallet_psc"] = round(available - amount_psc, 2)
        wallet["savings_psc"] = round(float(wallet.get("savings_psc", 0) or 0) + amount_psc, 2)
        wallet["balance"] = _wallet_total(wallet)
        _save_wallet(wallet)

        _admin_merge_wallet(
            address=wallet_addr,
            purchased_psc=wallet.get("wallet_psc", 0),
            bonus_psc=wallet.get("bonus_psc", 0),
            savings_psc=wallet.get("savings_psc", 0),
            deposit_psc=wallet.get("deposit_psc", 0),
        )
        _savings_ops_add({
            "type": "SAVINGS_MOVE_IN",
            "direction": "IN",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "wallet_psc_after": wallet["wallet_psc"],
            "savings_psc_after": wallet["savings_psc"],
            "created_at": _now(),
        })
        _admin_ledger_add({
            "type": "SAVINGS_MOVE_IN",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "time": _now(),
        })

        return jsonify({
            "success": True,
            "wallet": wallet_addr,
            "wallet_psc": wallet["wallet_psc"],
            "savings_psc": wallet["savings_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "deposit_psc": wallet.get("deposit_psc", 0),
            "balance": wallet["balance"],
            "moved_psc": amount_psc,
            "moved_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": (f"Moved {amount_psc:.2f} PSC (KES {amount_psc * PSC_TO_KES_RATE:.2f}) "
                        f"into savings."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/savings/move_out", methods=["POST"])
def api_wallet_savings_move_out():
    if not WALLET_SAVINGS_ENABLED:
        return jsonify({"success": False,
                        "message": "Savings is disabled (WALLET_SAVINGS_ENABLED=0)."}), 503
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()
        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        amount_psc = round(float(data.get("amount_psc") or 0), 2)
        if amount_psc < WALLET_SAVINGS_MIN_MOVE_PSC:
            return jsonify({"success": False,
                            "message": f"Minimum move-out is {WALLET_SAVINGS_MIN_MOVE_PSC} PSC."}), 400

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        savings = round(float(wallet.get("savings_psc", 0) or 0), 2)
        if savings + 1e-9 < amount_psc:
            return jsonify({
                "success": False,
                "message": (f"Insufficient savings. You have {savings:.2f} PSC in savings, "
                            f"cannot move {amount_psc:.2f} PSC out."),
                "savings_psc": savings,
            }), 400

        wallet["savings_psc"] = round(savings - amount_psc, 2)
        wallet["wallet_psc"] = round(float(wallet.get("wallet_psc", 0) or 0) + amount_psc, 2)
        wallet["balance"] = _wallet_total(wallet)
        _save_wallet(wallet)

        _admin_merge_wallet(
            address=wallet_addr,
            purchased_psc=wallet.get("wallet_psc", 0),
            bonus_psc=wallet.get("bonus_psc", 0),
            savings_psc=wallet.get("savings_psc", 0),
            deposit_psc=wallet.get("deposit_psc", 0),
        )
        _savings_ops_add({
            "type": "SAVINGS_MOVE_OUT",
            "direction": "OUT",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "wallet_psc_after": wallet["wallet_psc"],
            "savings_psc_after": wallet["savings_psc"],
            "created_at": _now(),
        })
        _admin_ledger_add({
            "type": "SAVINGS_MOVE_OUT",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "time": _now(),
        })

        return jsonify({
            "success": True,
            "wallet": wallet_addr,
            "wallet_psc": wallet["wallet_psc"],
            "savings_psc": wallet["savings_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "deposit_psc": wallet.get("deposit_psc", 0),
            "balance": wallet["balance"],
            "moved_psc": amount_psc,
            "moved_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": (f"Moved {amount_psc:.2f} PSC (KES {amount_psc * PSC_TO_KES_RATE:.2f}) "
                        f"back to your spendable balance."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# DEPOSIT PSC POCKET (HOLD-ONLY)
# ============================================================

WALLET_DEPOSIT_POCKET_ENABLED     = os.getenv("WALLET_DEPOSIT_POCKET_ENABLED", "1").strip() == "1"
WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC = float(os.getenv("WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC", "0.01") or 0.01)
WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC = float(os.getenv("WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC", "1.00") or 1.00)

WALLET_DEPOSIT_POCKET_OPS_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "wallet_deposit_pocket_ops.json"
)

_WALLET_DEPOSIT_POCKET_LOCK = threading.Lock()


def _deposit_pocket_ops_all():
    d = _jload(WALLET_DEPOSIT_POCKET_OPS_FILE, [])
    return d if isinstance(d, list) else []


def _deposit_pocket_ops_add(row):
    with _WALLET_DEPOSIT_POCKET_LOCK:
        rows = _deposit_pocket_ops_all()
        rows.append(row)
        _jsave(WALLET_DEPOSIT_POCKET_OPS_FILE, rows)


def _deposit_pocket_stats(wallet_addr):
    rows = [r for r in _deposit_pocket_ops_all() if r.get("wallet_address") == wallet_addr]
    total_in = sum(float(r.get("amount_psc") or 0) for r in rows if r.get("direction") == "IN")
    total_out = sum(float(r.get("amount_psc") or 0) for r in rows if r.get("direction") == "OUT")
    return {
        "in_psc": round(total_in, 2),
        "out_psc": round(total_out, 2),
        "net_psc": round(total_in - total_out, 2),
        "events": len(rows),
    }


@app.route("/api/wallet/deposit_pocket/<wallet_addr>", methods=["GET"])
def api_wallet_deposit_pocket_get(wallet_addr):
    wallet = get_wallet(wallet_addr)
    if not wallet:
        return jsonify({"success": False, "message": "Wallet not found."}), 404
    return jsonify({
        "success": True,
        "wallet": wallet_addr,
        "deposit_psc": round(float(wallet.get("deposit_psc", 0) or 0), 2),
        "deposit_value_kes": round(float(wallet.get("deposit_psc", 0) or 0) * PSC_TO_KES_RATE, 2),
        "wallet_psc": round(float(wallet.get("wallet_psc", 0) or 0), 2),
        "savings_psc": round(float(wallet.get("savings_psc", 0) or 0), 2),
        "bonus_psc": round(float(wallet.get("bonus_psc", 0) or 0), 2),
        "history": [r for r in _deposit_pocket_ops_all() if r.get("wallet_address") == wallet_addr],
        "stats": _deposit_pocket_stats(wallet_addr),
        "psc_to_kes_rate": PSC_TO_KES_RATE,
        "enabled": WALLET_DEPOSIT_POCKET_ENABLED,
        "min_move_psc": WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC,
        "min_leave_psc": WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC,
    })


@app.route("/api/wallet/deposit/move_in", methods=["POST"])
def api_wallet_deposit_move_in():
    if not WALLET_DEPOSIT_POCKET_ENABLED:
        return jsonify({"success": False,
                        "message": "Deposit pocket is disabled (WALLET_DEPOSIT_POCKET_ENABLED=0)."}), 503
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()
        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        amount_psc = round(float(data.get("amount_psc") or 0), 2)
        if amount_psc < WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC:
            return jsonify({"success": False,
                            "message": f"Minimum move-in is {WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC} PSC."}), 400

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
        if available - amount_psc < WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC - 1e-9:
            return jsonify({
                "success": False,
                "message": (f"At least {WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC:.2f} PSC must remain in your "
                            f"spendable balance. Available: {available:.2f} PSC. "
                            f"Maximum movable: {max(0.0, available - WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC):.2f} PSC."),
                "wallet_psc": available,
                "max_move_psc": round(max(0.0, available - WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC), 2),
            }), 400

        wallet["wallet_psc"] = round(available - amount_psc, 2)
        wallet["deposit_psc"] = round(float(wallet.get("deposit_psc", 0) or 0) + amount_psc, 2)
        wallet["balance"] = _wallet_total(wallet)
        _save_wallet(wallet)

        _admin_merge_wallet(
            address=wallet_addr,
            purchased_psc=wallet.get("wallet_psc", 0),
            bonus_psc=wallet.get("bonus_psc", 0),
            savings_psc=wallet.get("savings_psc", 0),
            deposit_psc=wallet.get("deposit_psc", 0),
        )
        _deposit_pocket_ops_add({
            "type": "DEPOSIT_POCKET_MOVE_IN",
            "direction": "IN",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "wallet_psc_after": wallet["wallet_psc"],
            "deposit_psc_after": wallet["deposit_psc"],
            "created_at": _now(),
        })
        _admin_ledger_add({
            "type": "DEPOSIT_POCKET_MOVE_IN",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "time": _now(),
        })

        return jsonify({
            "success": True,
            "wallet": wallet_addr,
            "wallet_psc": wallet["wallet_psc"],
            "savings_psc": wallet["savings_psc"],
            "deposit_psc": wallet["deposit_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "balance": wallet["balance"],
            "moved_psc": amount_psc,
            "moved_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": (f"Moved {amount_psc:.2f} PSC (KES {amount_psc * PSC_TO_KES_RATE:.2f}) "
                        f"into the Deposit PSC pocket. It is hold-only and not spent by shopping."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/deposit/move_out", methods=["POST"])
def api_wallet_deposit_move_out():
    if not WALLET_DEPOSIT_POCKET_ENABLED:
        return jsonify({"success": False,
                        "message": "Deposit pocket is disabled (WALLET_DEPOSIT_POCKET_ENABLED=0)."}), 503
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()
        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        amount_psc = round(float(data.get("amount_psc") or 0), 2)
        if amount_psc < WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC:
            return jsonify({"success": False,
                            "message": f"Minimum move-out is {WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC} PSC."}), 400

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        deposit_avail = round(float(wallet.get("deposit_psc", 0) or 0), 2)
        if deposit_avail + 1e-9 < amount_psc:
            return jsonify({
                "success": False,
                "message": (f"Insufficient deposit PSC. You have {deposit_avail:.2f} PSC in the "
                            f"deposit pocket, cannot move {amount_psc:.2f} PSC out."),
                "deposit_psc": deposit_avail,
            }), 400

        wallet["deposit_psc"] = round(deposit_avail - amount_psc, 2)
        wallet["wallet_psc"] = round(float(wallet.get("wallet_psc", 0) or 0) + amount_psc, 2)
        wallet["balance"] = _wallet_total(wallet)
        _save_wallet(wallet)

        _admin_merge_wallet(
            address=wallet_addr,
            purchased_psc=wallet.get("wallet_psc", 0),
            bonus_psc=wallet.get("bonus_psc", 0),
            savings_psc=wallet.get("savings_psc", 0),
            deposit_psc=wallet.get("deposit_psc", 0),
        )
        _deposit_pocket_ops_add({
            "type": "DEPOSIT_POCKET_MOVE_OUT",
            "direction": "OUT",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "wallet_psc_after": wallet["wallet_psc"],
            "deposit_psc_after": wallet["deposit_psc"],
            "created_at": _now(),
        })
        _admin_ledger_add({
            "type": "DEPOSIT_POCKET_MOVE_OUT",
            "wallet_address": wallet_addr,
            "amount_psc": amount_psc,
            "amount_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "time": _now(),
        })

        return jsonify({
            "success": True,
            "wallet": wallet_addr,
            "wallet_psc": wallet["wallet_psc"],
            "savings_psc": wallet["savings_psc"],
            "deposit_psc": wallet["deposit_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "balance": wallet["balance"],
            "moved_psc": amount_psc,
            "moved_kes": round(amount_psc * PSC_TO_KES_RATE, 2),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": (f"Moved {amount_psc:.2f} PSC (KES {amount_psc * PSC_TO_KES_RATE:.2f}) "
                        f"out of the Deposit PSC pocket into spendable balance."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/overview/<wallet_addr>", methods=["GET"])
def api_wallet_overview(wallet_addr):
    wallet = get_wallet(wallet_addr)
    if not wallet:
        return jsonify({"success": False, "message": "Wallet not found."}), 404

    withdraw_used = _wallet_withdraw_today_kes(wallet_addr)
    deposit_today = _wallet_deposit_today_kes(wallet_addr)
    transfer_today = _wallet_transfer_today_psc(wallet_addr)

    return jsonify({
        "success": True,
        "wallet": wallet_addr,
        "balances": {
            "wallet_psc": round(float(wallet.get("wallet_psc", 0) or 0), 2),
            "savings_psc": round(float(wallet.get("savings_psc", 0) or 0), 2),
            "deposit_psc": round(float(wallet.get("deposit_psc", 0) or 0), 2),
            "bonus_psc": round(float(wallet.get("bonus_psc", 0) or 0), 2),
            "daily_login_bonus_psc": round(float(wallet.get("daily_login_bonus_psc", 0) or 0), 2),
            "held_psc": round(float(wallet.get("held_psc", 0) or 0), 2),
            "total_psc": round(_wallet_total(wallet), 2),
            "total_kes": round(_wallet_total(wallet) * PSC_TO_KES_RATE, 2),
        },
        "values_kes": {
            "wallet_psc": round(float(wallet.get("wallet_psc", 0) or 0) * PSC_TO_KES_RATE, 2),
            "savings_psc": round(float(wallet.get("savings_psc", 0) or 0) * PSC_TO_KES_RATE, 2),
            "deposit_psc": round(float(wallet.get("deposit_psc", 0) or 0) * PSC_TO_KES_RATE, 2),
            "bonus_psc": round(float(wallet.get("bonus_psc", 0) or 0) * PSC_TO_KES_RATE, 2),
            "total_psc": round(_wallet_total(wallet) * PSC_TO_KES_RATE, 2),
        },
        "daily_usage": {
            "withdraw_used_kes": withdraw_used,
            "withdraw_max_kes": WALLET_WITHDRAW_DAILY_MAX_KES,
            "withdraw_remaining_kes": round(max(0.0, WALLET_WITHDRAW_DAILY_MAX_KES - withdraw_used), 2),
            "deposit_today_kes": deposit_today,
            "deposit_max_kes": WALLET_DEPOSIT_MAX_KES,
            "transfer_today_psc": transfer_today,
            "transfer_daily_max_psc": WALLET_TRANSFER_DAILY_MAX_PSC,
        },
        "limits": {
            "deposit_max_kes": WALLET_DEPOSIT_MAX_KES,
            "withdraw_daily_max_kes": WALLET_WITHDRAW_DAILY_MAX_KES,
            "transfer_min_psc": WALLET_TRANSFER_MIN_PSC,
            "transfer_max_psc": WALLET_TRANSFER_MAX_PSC,
            "transfer_daily_max_psc": WALLET_TRANSFER_DAILY_MAX_PSC,
            "savings_min_move_psc": WALLET_SAVINGS_MIN_MOVE_PSC,
            "savings_min_leave_psc": WALLET_SAVINGS_MIN_LEAVE_PSC,
            "deposit_pocket_min_move_psc": WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC,
            "deposit_pocket_min_leave_psc": WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC,
            "min_balance_to_shop": MIN_BALANCE_TO_SHOP,
        },
        "psc_to_kes_rate": PSC_TO_KES_RATE,
        "savings_enabled": WALLET_SAVINGS_ENABLED,
        "deposit_pocket_enabled": WALLET_DEPOSIT_POCKET_ENABLED,
    })


@app.route("/api/wallet/ui/<wallet_addr>", methods=["GET"])
def api_wallet_ui(wallet_addr):
    wallet = get_wallet(wallet_addr)
    if not wallet:
        return jsonify({"success": False, "message": "Wallet not found."}), 404

    balances = {
        "wallet_psc": round(float(wallet.get("wallet_psc", 0) or 0), 2),
        "savings_psc": round(float(wallet.get("savings_psc", 0) or 0), 2),
        "deposit_psc": round(float(wallet.get("deposit_psc", 0) or 0), 2),
        "bonus_psc": round(float(wallet.get("bonus_psc", 0) or 0), 2),
        "daily_login_bonus_psc": round(float(wallet.get("daily_login_bonus_psc", 0) or 0), 2),
        "held_psc": round(float(wallet.get("held_psc", 0) or 0), 2),
        "total_psc": round(_wallet_total(wallet), 2),
        "total_kes": round(_wallet_total(wallet) * PSC_TO_KES_RATE, 2),
    }

    # Payment gateways removed â€” "deposit" action is intentionally omitted.
    actions = [
        {
            "key": "transfer",
            "label": "Send to another user",
            "icon": "ðŸ“¤",
            "endpoint": "/api/wallet/transfer",
            "method": "POST",
            "fields": ["recipient", "amount_psc"],
            "min_psc": WALLET_TRANSFER_MIN_PSC,
            "max_psc": WALLET_TRANSFER_MAX_PSC,
            "daily_max_psc": WALLET_TRANSFER_DAILY_MAX_PSC,
            "hint": "Recipient can be a phone number or a PSC wallet address.",
        },
        {
            "key": "withdraw",
            "label": "Withdraw to bank / M-Pesa",
            "icon": "ðŸ“¥",
            "endpoint": "/api/wallet/withdraw/highvalue",
            "method": "POST",
            "fields": ["amount_psc", "method", "destination", "bank_code"],
            "daily_max_kes": WALLET_WITHDRAW_DAILY_MAX_KES,
            "hint": "Admin confirmation is required before funds leave.",
        },
        {
            "key": "save",
            "label": "Move to Savings",
            "icon": "ðŸ”’",
            "endpoint": "/api/wallet/savings/move_in",
            "method": "POST",
            "fields": ["amount_psc"],
            "min_move_psc": WALLET_SAVINGS_MIN_MOVE_PSC,
            "min_leave_psc": WALLET_SAVINGS_MIN_LEAVE_PSC,
            "enabled": WALLET_SAVINGS_ENABLED,
            "hint": "Park PSC safely; savings is never touched by shopping.",
        },
        {
            "key": "unsave",
            "label": "Move back from Savings",
            "icon": "ðŸ”“",
            "endpoint": "/api/wallet/savings/move_out",
            "method": "POST",
            "fields": ["amount_psc"],
            "min_move_psc": WALLET_SAVINGS_MIN_MOVE_PSC,
            "enabled": WALLET_SAVINGS_ENABLED,
            "hint": "Return PSC from savings to your spendable balance.",
        },
        {
            "key": "deposit_psc_in",
            "label": "Move to Deposit PSC",
            "icon": "ðŸ§ ",
            "endpoint": "/api/wallet/deposit/move_in",
            "method": "POST",
            "fields": ["amount_psc"],
            "min_move_psc": WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC,
            "min_leave_psc": WALLET_DEPOSIT_POCKET_MIN_LEAVE_PSC,
            "enabled": WALLET_DEPOSIT_POCKET_ENABLED,
            "hint": "Hold-only pocket; never spent by shopping.",
        },
        {
            "key": "deposit_psc_out",
            "label": "Move back from Deposit PSC",
            "icon": "ðŸ§ ",
            "endpoint": "/api/wallet/deposit/move_out",
            "method": "POST",
            "fields": ["amount_psc"],
            "min_move_psc": WALLET_DEPOSIT_POCKET_MIN_MOVE_PSC,
            "enabled": WALLET_DEPOSIT_POCKET_ENABLED,
            "hint": "Return PSC from deposit pocket to spendable balance.",
        },
        {
            "key": "redeem_daily_bonus",
            "label": "Redeem daily bonus",
            "icon": "ðŸŽ",
            "endpoint": "/api/wallet/redeem_daily_bonus",
            "method": "POST",
            "fields": [],
            "hint": "Move your daily bonus into spendable balance.",
        },
    ]

    return jsonify({
        "success": True,
        "wallet": wallet_addr,
        "balances": balances,
        "actions": actions,
        "psc_to_kes_rate": PSC_TO_KES_RATE,
        "currency": "KES",
        "min_balance_to_shop": MIN_BALANCE_TO_SHOP,
        "updated_at": _now(),
        "payment_gateways_enabled": False,
    })


# ============================================================
# CATEGORY IMAGES, VENDOR INFO, SEARCH
# ============================================================

@app.route("/api/category_images")
def api_category_images():
    try:
        result = {}

        for cat in CATEGORY_GROUPS:
            key = cat["key"]

            # Cache bypassed to allow live 15s updates

            products = _cache_get(f"products::all::{cat['query'].lower()}") or []
            if not products:
                products = _cache_get(f"products::{cat['query'].lower()}") or []
            if not products:
                products = _cache_get_soft(f"products::all::{cat['query'].lower()}") or []

            pick = None
            _kw = [w for w in cat["query"].lower().split() if len(w) >= 3]
            valid_picks = []
            for p in products:
                if not p or not p.get("image"):
                    continue
                if _kw:
                    _hay = (str(p.get("name", "")) + " " +
                            str(p.get("category", ""))).lower()
                    if not any(w in _hay for w in _kw):
                        continue
                valid_picks.append(p)
            
            if valid_picks:
                pick = random.choice(valid_picks)

            if pick:
                _CATEGORY_IMAGE_CACHE[key] = {
                    "ts":    time.time(),
                    "image": pick.get("image", ""),
                    "name":  pick.get("name", ""),
                }
                result[key] = {
                    "image": pick.get("image", ""),
                    "name":  pick.get("name", ""),
                    "emoji": cat.get("emoji", ""),
                }
                continue

            try:
                _background_refresh_products(
                    cat["query"],
                    vendor=None,
                    cache_key=f"products::all::{cat['query'].lower()}",
                )
            except Exception as e:
                print(f"[CAT-IMG] background refresh schedule failed for {key}: {e}")

            if not pick:
                _kw = [w for w in cat["query"].lower().split() if len(w) >= 3]
                for _p in _PRODUCT_CACHE.values():
                    if not _p or not _p.get("image"):
                        continue
                    _hay = (str(_p.get("name", "")) + " " +
                            str(_p.get("category", ""))).lower()
                    if _kw and all(w in _hay for w in _kw):
                        pick = _p
                        break

            if not pick:
                try:
                    for _it in _load_seller_items():
                        if _it.get("status") != "ACTIVE" or not _it.get("image"):
                            continue
                        if (str(_it.get("category_query", "")).lower() == cat["query"].lower()
                                or str(_it.get("category_key", "")).lower() == cat["key"].lower()):
                            pick = _it
                            break
                        _hay2 = (str(_it.get("name", "")) + " " +
                                 str(_it.get("description", "")) + " " +
                                 " ".join(str(k) for k in (_it.get("keywords") or []))).lower()
                        if _kw and any(w in _hay2 for w in _kw):
                            pick = _it
                            break
                except Exception:
                    pass

            if pick:
                _img = pick.get("image", "")
                _nm  = pick.get("name", "")
                _CATEGORY_IMAGE_CACHE[key] = {"ts": time.time(), "image": _img, "name": _nm}
                result[key] = {"image": _img, "name": _nm, "emoji": cat.get("emoji", "")}
                continue

            fallback_img = FALLBACK_CATEGORY_IMAGES.get(key, "")
            if fallback_img:
                _CATEGORY_IMAGE_CACHE[key] = {"ts": time.time(), "image": fallback_img, "name": cat["label"]}
                result[key] = {"image": fallback_img, "name": cat["label"], "emoji": cat.get("emoji", "")}
                continue

            result[key] = {"image": "", "name": "", "emoji": cat.get("emoji", "")}

        return jsonify({"success": True, "images": result,
                        "psc_to_kes_rate": PSC_TO_KES_RATE,
                        "cached_only": True})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/vendors")
def api_vendors():
    return jsonify({
        "success": True,
        "psc_to_kes_rate": PSC_TO_KES_RATE,
        "vendors": [],
    })


@app.route("/api/search")
def api_search():
    try:
        raw_q = request.args.get("q", "").strip()
        try:
            limit = int(request.args.get("limit", 40))
        except (TypeError, ValueError):
            limit = 40
        if limit < 1:
            limit = 1
        if limit > 1000:
            limit = 1000

        vendor_hint, _ = _extract_vendor_hint(raw_q)
        q = _normalize_search_query(raw_q)

        if not q:
            return jsonify({
                "success": False,
                "message": "Type something to search.",
                "products": [],
            }), 400

        products = load_products(q, vendor=vendor_hint)
        _register_products(products)
        products = _tag_new(products)
        products = products[:limit]

        return jsonify({
            "success": True,
            "query": q,
            "vendor": "all",
            "count": len(products),
            "products": _strip_products_for_client(products),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "cached": True,
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e), "products": []}), 500


@app.route("/")
def index():
    raw_query = request.args.get("q", "").strip()
    category_key = request.args.get("category", "").strip()

    vendor, _ = _extract_vendor_hint(raw_query)
    query = _normalize_search_query(raw_query)

    if category_key:
        cat = next((c for c in CATEGORY_GROUPS if c["key"] == category_key), None)
        if cat:
            products = load_products(cat["query"], vendor=vendor)
            products = _tag_new(products)
            _register_products(products)

            wallet = session.get("wallet", "")
            w = get_wallet(wallet) if wallet else None
            if wallet:
                try:
                    _grant_daily_visit_bonus(wallet)
                    w = get_wallet(wallet) or w
                except Exception as _vb_e:
                    print(f"[PSC VISIT-BONUS] index(category) failed: {_vb_e}")
            balance = round(w["balance"], 2) if w else 0
            user = session.get("user", None)

            hero_cache_key = f"hero::category::{category_key}"
            hero = _cache_get(hero_cache_key)
            if hero is None:
                hero = _build_hero(products)
                _cache_set(hero_cache_key, hero)

            return render_template(
                "shop.html",
                products=_strip_products_for_client(products),
                query=cat["query"],
                active_category=category_key,
                active_category_label=cat["label"],
                categories=_get_shuffled_categories(),
                new_items=[],
                top_selling=[],
                hero_items=_strip_products_for_client(hero),
                wallet=wallet,
                balance=balance,
                user=user,
            )

    if query:
        products = load_products(query, vendor=vendor)

        if not products and query and " " in query:
            broader = query.split()[0]
            if broader and broader.lower() != query.lower():
                print(f"[PSC SEARCH] '{query}' empty, retrying with '{broader}'")
                products = load_products(broader, vendor=vendor)

        products = _tag_new(products)
        _register_products(products)

        big_pool = products[:24]
        top_selling = big_pool[:12]
        new_items = [p for p in big_pool if p.get("is_new")][:8] or big_pool[12:16]
        hero_items = _build_hero(products)
    else:
        big_pool = load_products_multi(
            ["smart tv", "smartphone", "laptop", "headphones"],
            per_query=10,
            vendor=None,
        )
        big_pool = _tag_new(big_pool)
        _register_products(big_pool)

        top_selling = big_pool[:12]
        new_items = ([p for p in big_pool if p.get("is_new")][:8]
                     or big_pool[12:16])
        products = big_pool[:20]

        hero_cache_key = "hero::home"
        hero_items = _cache_get(hero_cache_key)
        if hero_items is None:
            hero_pool = []
            seen = set()
            for src in (new_items, top_selling, products):
                for p in src:
                    if not p.get("image"):
                        continue
                    k = p["name"].strip().lower()[:50]
                    if k in seen:
                        continue
                    seen.add(k)
                    hero_pool.append(p)
            random.shuffle(hero_pool)
            hero_items = hero_pool[:10]
            _cache_set(hero_cache_key, hero_items)

    wallet = session.get("wallet", "")
    w = get_wallet(wallet) if wallet else None
    if wallet:
        try:
            _grant_daily_visit_bonus(wallet)
            w = get_wallet(wallet) or w
        except Exception as _vb_e:
            print(f"[PSC VISIT-BONUS] index failed: {_vb_e}")
    balance = round(w["balance"], 2) if w else 0
    user = session.get("user", None)

    return render_template(
        "shop.html",
        products=_strip_products_for_client(products),
        query=query,
        active_category="",
        active_category_label="",
        categories=_get_shuffled_categories(),
        new_items=_strip_products_for_client(new_items),
        top_selling=_strip_products_for_client(top_selling),
        hero_items=_strip_products_for_client(hero_items),
        wallet=wallet,
        balance=balance,
        user=user,
    )


@app.route("/api/account/register", methods=["POST"])
def api_account_register():
    try:
        data = request.get_json() or {}
        name = (data.get("name") or "").strip()
        phone = (data.get("phone") or "").strip()
        email = (data.get("email") or "").strip()
        password = (data.get("password") or "").strip()

        if not name or not phone or not password:
            return jsonify({"success": False, "message": "Name, phone and password are required."})

        clients = _load_clients()
        key = _normalize_phone(phone)

        if key in clients and clients[key].get("password"):
            return jsonify({"success": False,
                            "message": "An account with this phone already exists. Please log in."})

        existing_for_phone = clients.get(key, {}) or {}

        if existing_for_phone.get("email") and email:
            if _normalize_email(existing_for_phone.get("email", "")) != _normalize_email(email):
                return jsonify({
                    "success": False,
                    "message": ("This phone number is already linked to a different email. "
                                "Please log in with the registered email or use a different phone.")
                })

        if email and not _email_belongs_to_phone(email, phone):
            return jsonify({
                "success": False,
                "message": ("This email is already registered to a different phone number. "
                            "Please log in with that phone or use a different email.")
            })

        if email and _email_in_use(email, except_key=key):
            return jsonify({"success": False,
                            "message": "An account with this email already exists."})

        wallet = create_client_wallet()

        existing = clients.get(key, {})
        existing.update({
            "name": name,
            "phone": phone,
            "email": email,
            "password": generate_password_hash(password),
            "wallet_address": wallet["address"],
            "registered_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "first_seen_at": existing.get(
                "first_seen_at",
                datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            ),
        })

        clients[key] = existing
        _save_clients(clients)

        _admin_merge_wallet(
            address=wallet["address"],
            name=name, phone=phone, email=email,
            purchased_psc=wallet.get("wallet_psc", 0),
            bonus_psc=wallet.get("bonus_psc", 0),
            savings_psc=wallet.get("savings_psc", 0),
            deposit_psc=wallet.get("deposit_psc", 0),
        )

        session["user"] = {"name": name, "phone": phone, "email": email}
        session["wallet"] = wallet["address"]
        session["verified_phone"] = _normalize_phone(phone)
        session["verified_wallet"] = wallet["address"]
        session.permanent = True

        return jsonify({
            "success": True,
            "message": f"Welcome {name}! You received {WELCOME_BONUS} bonus PSC.",
            "wallet": wallet["address"],
            "balance": wallet["balance"],
            "wallet_psc": wallet["wallet_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "savings_psc": wallet.get("savings_psc", 0),
            "deposit_psc": wallet.get("deposit_psc", 0),
            "daily_login_bonus_psc": wallet.get("daily_login_bonus_psc", 0),
            "user": session["user"],
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/account/login", methods=["POST"])
@limiter.limit("5 per minute")
def api_account_login():
    try:
        data = request.get_json() or {}
        phone = (data.get("phone") or "").strip()
        password = (data.get("password") or "").strip()

        if not phone or not password:
            return jsonify({"success": False, "message": "Phone and password are required."})

        clients = _load_clients()
        client = clients.get(_normalize_phone(phone))

        if not client:
            _audit_login(phone, False, "no_account")
            return jsonify({"success": False,
                            "message": "No account found with that phone number."})

        stored = client.get("password", "")
        try:
            ok_pw = check_password_hash(stored, password)
        except Exception:
            ok_pw = False
        if not ok_pw:
            _audit_login(phone, False, "bad_password")
            return jsonify({"success": False, "message": "Incorrect password."})

        wallet_addr = client.get("wallet_address", "")
        wallet = get_wallet(wallet_addr) if wallet_addr else None
        if not wallet:
            _audit_login(phone, False, "wallet_missing")
            return jsonify({"success": False, "message": "Wallet not found for this account."})

        stored_phone = _normalize_phone(client.get("phone", ""))
        typed_phone = _normalize_phone(phone)
        if stored_phone and typed_phone != stored_phone:
            _audit_login(phone, False, "phone_mismatch")
            return jsonify({"success": False,
                            "message": "This account is not recognised."})

        _, daily_bonus_message, wallet = add_daily_login_bonus(wallet_addr)
        balance = round(wallet["balance"], 2)

        session["user"] = {
            "name": client.get("name", ""),
            "phone": client.get("phone", phone),
            "email": client.get("email", ""),
        }
        session["wallet"] = wallet_addr
        session["verified_phone"] = _normalize_phone(phone)
        session["verified_wallet"] = wallet_addr
        session.permanent = True

        _audit_login(phone, True, "ok")

        return jsonify({
            "success": True,
            "message": f"Welcome back, {client.get('name', '')}! {daily_bonus_message}",
            "wallet": wallet_addr,
            "balance": balance,
            "wallet_psc": wallet["wallet_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "savings_psc": wallet.get("savings_psc", 0),
            "deposit_psc": wallet.get("deposit_psc", 0),
            "daily_login_bonus_psc": wallet.get("daily_login_bonus_psc", 0),
            "user": session["user"],
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/account/logout", methods=["POST"])
def api_account_logout():
    session.clear()
    session.modified = True
    resp = jsonify({"success": True, "message": "Logged out."})
    resp.delete_cookie(app.config.get("SESSION_COOKIE_NAME", "session"))
    return resp


@app.route("/api/account/me")
def api_account_me():
    user = session.get("user")
    wallet_addr = session.get("wallet", "")
    if not user:
        return jsonify({"success": False, "logged_in": False})

    wallet = get_wallet(wallet_addr) if wallet_addr else None
    if wallet_addr:
        try:
            _grant_daily_visit_bonus(wallet_addr)
            wallet = get_wallet(wallet_addr) or wallet
        except Exception as _vb_e:
            print(f"[PSC VISIT-BONUS] account/me failed: {_vb_e}")
    balance = round(wallet["balance"], 2) if wallet else 0

    return jsonify({
        "success": True,
        "logged_in": True,
        "user": user,
        "wallet": wallet_addr,
        "balance": balance,
        "wallet_psc": wallet.get("wallet_psc", 0) if wallet else 0,
        "bonus_psc": wallet.get("bonus_psc", 0) if wallet else 0,
        "savings_psc": wallet.get("savings_psc", 0) if wallet else 0,
        "deposit_psc": wallet.get("deposit_psc", 0) if wallet else 0,
        "daily_login_bonus_psc": wallet.get("daily_login_bonus_psc", 0) if wallet else 0,
        "psc_to_kes_rate": PSC_TO_KES_RATE,
    })


@app.route("/api/wallet/auto_create", methods=["POST"])
def api_auto_create_wallet():
    wallet = create_client_wallet()
    session["wallet"] = wallet["address"]

    return jsonify({
        "success": True,
        "address": wallet["address"],
        "balance": wallet["balance"],
        "wallet_psc": wallet["wallet_psc"],
        "bonus_psc": wallet["bonus_psc"],
        "savings_psc": wallet.get("savings_psc", 0),
        "deposit_psc": wallet.get("deposit_psc", 0),
        "bonus": WELCOME_BONUS,
        "psc_to_kes_rate": PSC_TO_KES_RATE,
    })


@app.route("/api/wallet/purchase", methods=["POST"])
def api_wallet_purchase():
    """Admin-only PSC credit (no external payment gateway)."""
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({
            "success": False,
            "message": ("This endpoint is for the admin wallet system only. "
                        "Payment gateways are disabled. Ask the admin to "
                        "credit your account or receive P2P transfers.")
        }), 403

    try:
        data = request.get_json() or {}
        wallet_addr = data.get("wallet")
        if not wallet_addr:
            return jsonify({"success": False, "message": "wallet is required."})

        try:
            kes_amount = round(float(data.get("kes_amount", 0)), 2)
        except (TypeError, ValueError):
            kes_amount = 0.0
        if kes_amount <= 0:
            return jsonify({"success": False, "message": "KES purchase amount must be greater than zero."})

        psc_amount = round(kes_amount / PSC_TO_KES_RATE, 2)
        if psc_amount <= 0:
            return jsonify({"success": False, "message": "Purchase amount is too small to purchase PSC."})

        payment_reference = str(data.get("payment_reference", "")).strip()
        _target = _normalize_credit_target(data.get("target") or "spendable")

        ok, msg, wallet = _add_psc_to_target(
            wallet_addr, psc_amount,
            target=_target, kes_amount=kes_amount,
            payment_reference=payment_reference,
            audit_type="ADMIN_CREDIT",
        )
        if not ok:
            return jsonify({"success": False, "message": msg})

        return jsonify({
            "success": True,
            "message": f"Credited {psc_amount:.2f} PSC for KES {kes_amount:.2f}.",
            "wallet": wallet["address"],
            "purchased_psc": psc_amount,
            "wallet_psc": wallet["wallet_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "savings_psc": wallet.get("savings_psc", 0),
            "deposit_psc": wallet.get("deposit_psc", 0),
            "balance": wallet["balance"],
            "kes_amount": kes_amount,
            "target": _target,
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "payment_reference": payment_reference,
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/redeem_daily_bonus", methods=["POST"])
def api_wallet_redeem_daily_bonus():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = data.get("wallet") or session_wallet

        if not wallet_addr:
            return jsonify({"success": False, "message": "Please log in or provide a wallet."})
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet does not match the logged-in account."})

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"})

        redeemable = round(float(wallet.get("daily_login_bonus_psc", 0) or 0), 2)
        if redeemable <= 0:
            return jsonify({"success": False,
                            "message": "No daily bonus available to redeem.",
                            "redeemable_psc": 0})

        wallet["wallet_psc"] = round(float(wallet.get("wallet_psc", 0) or 0) + redeemable, 2)
        wallet["daily_login_bonus_psc"] = 0.0
        wallet["balance"] = _wallet_total(wallet)

        wallet.setdefault("purchase_history", [])
        wallet["purchase_history"].append({
            "psc": redeemable,
            "kes": round(redeemable * PSC_TO_KES_RATE, 2),
            "payment_reference": "DAILY_BONUS_REDEEM",
            "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        })

        _save_wallet(wallet)
        _admin_merge_wallet(
            address=wallet_addr,
            purchased_psc=wallet.get("wallet_psc", 0),
            bonus_psc=wallet.get("bonus_psc", 0),
            savings_psc=wallet.get("savings_psc", 0),
            deposit_psc=wallet.get("deposit_psc", 0),
        )

        return jsonify({
            "success": True,
            "message": f"Redeemed {redeemable:.2f} PSC into your purchased balance.",
            "redeemed_psc": redeemable,
            "wallet_psc": wallet["wallet_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "savings_psc": wallet.get("savings_psc", 0),
            "deposit_psc": wallet.get("deposit_psc", 0),
            "daily_login_bonus_psc": wallet["daily_login_bonus_psc"],
            "balance": wallet["balance"],
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/purchase_request", methods=["POST"])
def api_wallet_purchase_request():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = data.get("wallet") or session_wallet

        if not wallet_addr:
            return jsonify({"success": False, "message": "Please log in or provide a wallet."})
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet does not match the logged-in account."})

        try:
            kes_amount = round(float(data.get("kes_amount", 0)), 2)
        except (TypeError, ValueError):
            kes_amount = 0.0

        if kes_amount <= 0:
            return jsonify({"success": False, "message": "Enter how many KSh of PSC you want to buy."})

        psc_amount = round(kes_amount / PSC_TO_KES_RATE, 2)
        if psc_amount <= 0:
            return jsonify({"success": False, "message": "Amount too small."})

        payment_reference = str(data.get("payment_reference", "")).strip()
        mpesa_number = str(data.get("mpesa_number", "")).strip()

        client = None
        clients = _load_clients()
        for key, c in clients.items():
            if c.get("wallet_address") == wallet_addr:
                client = c
                break

        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        request_id = "PR-" + datetime.now().strftime("%Y%m%d%H%M%S%f")

        entry = {
            "type": "PURCHASE_REQUEST",
            "request_id": request_id,
            "wallet_address": wallet_addr,
            "name": (client or {}).get("name", ""),
            "phone": (client or {}).get("phone", ""),
            "email": (client or {}).get("email", ""),
            "mpesa_number": mpesa_number,
            "amount_kes": kes_amount,
            "amount_psc": psc_amount,
            "payment_reference": payment_reference,
            "status": "PENDING",
            "time": now,
        }

        _admin_ledger_add(entry)

        return jsonify({
            "success": True,
            "request_id": request_id,
            "amount_kes": kes_amount,
            "amount_psc": psc_amount,
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": (f"Purchase request {request_id} sent to admin. "
                        f"You will be credited {psc_amount:.2f} PSC manually."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/withdraw_request", methods=["POST"])
def api_wallet_withdraw_request():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = data.get("wallet") or session_wallet

        if not wallet_addr:
            return jsonify({"success": False, "message": "Please log in or provide a wallet."})
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet does not match the logged-in account."})

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"})

        try:
            amount_psc = round(float(data.get("amount_psc", 0)), 2)
        except (TypeError, ValueError):
            amount_psc = 0.0

        available_psc = round(float(wallet.get("wallet_psc", 0) or 0), 2)

        if amount_psc <= 0:
            return jsonify({"success": False, "message": "Enter the amount of purchased PSC to withdraw."})

        if amount_psc > available_psc:
            return jsonify({
                "success": False,
                "message": (
                    f"Withdrawal amount exceeds your Purchased/Savings balance. "
                    f"You have {available_psc:.2f} PSC."
                ),
                "wallet_psc": available_psc,
                "wallet_value_kes": round(available_psc * PSC_TO_KES_RATE, 2),
            })

        amount_kes = round(amount_psc * PSC_TO_KES_RATE, 2)
        verified_phone = session.get("verified_phone", "")
        client = get_client_by_phone(verified_phone) if verified_phone else None
        request_id = "WR-" + datetime.now().strftime("%Y%m%d%H%M%S%f")
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        entry = {
            "type": "WITHDRAWAL_REQUEST",
            "request_id": request_id,
            "wallet_address": wallet_addr,
            "name": (client or {}).get("name", ""),
            "phone": (client or {}).get("phone", ""),
            "email": (client or {}).get("email", ""),
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "payout_method": str(data.get("payout_method", "M-Pesa")).strip() or "M-Pesa",
            "payout_number": str(data.get("payout_number", "")).strip(),
            "status": "PENDING",
            "time": now,
        }

        _admin_ledger_add(entry)

        return jsonify({
            "success": True,
            "request_id": request_id,
            "status": "PENDING",
            "amount_psc": amount_psc,
            "amount_kes": amount_kes,
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": (
                f"Withdrawal request {request_id} sent to admin. "
                f"Requested value: KES {amount_kes:.2f}."
            ),
        })

    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/balance/<address>")
def api_balance(address):
    wallet = get_wallet(address)
    if not wallet:
        return jsonify({"address": address, "balance": 0})

    return jsonify({
        "address": address,
        "balance": wallet["balance"],
        "wallet_psc": wallet.get("wallet_psc", 0),
        "bonus_psc": wallet.get("bonus_psc", 0),
        "savings_psc": wallet.get("savings_psc", 0),
        "deposit_psc": wallet.get("deposit_psc", 0),
        "daily_login_bonus_psc": wallet.get("daily_login_bonus_psc", 0),
        "wallet_value_kes": round(wallet.get("wallet_psc", 0) * PSC_TO_KES_RATE, 2),
        "bonus_value_kes": round(wallet.get("bonus_psc", 0) * PSC_TO_KES_RATE, 2),
        "savings_value_kes": round(wallet.get("savings_psc", 0) * PSC_TO_KES_RATE, 2),
        "deposit_value_kes": round(wallet.get("deposit_psc", 0) * PSC_TO_KES_RATE, 2),
        "psc_to_kes_rate": PSC_TO_KES_RATE,
    })


@app.route("/api/client/lookup", methods=["POST"])
def api_client_lookup():
    try:
        data = request.get_json() or {}
        phone = data.get("phone", "").strip()
        shipping = data.get("shipping", {}) or {}

        if not phone:
            return jsonify({"success": False, "message": "Phone number is required."})

        _logged_in_user = session.get("user")
        if not _logged_in_user:
            return jsonify({
                "success": False,
                "message": ("Please log in first before checking out. "
                            "You need an account to place an order.")
            })

        _logged_in_phone = _normalize_phone(_logged_in_user.get("phone", ""))
        _typed_phone_norm = _normalize_phone(phone)

        if _logged_in_phone and _typed_phone_norm != _logged_in_phone:
            return jsonify({
                "success": False,
                "message": ("You are logged in with a different phone number. "
                            "Please use your own number, or log out and log "
                            "in with the correct account.")
            })

        client = get_client_by_phone(phone)

        if client and client.get("wallet_address"):
            stored_phone = _normalize_phone(client.get("phone", ""))
            typed_phone = _normalize_phone(phone)

            if stored_phone and typed_phone != stored_phone:
                return jsonify({
                    "success": False,
                    "message": ("This number is tied to a different customer "
                                "account. Please use the phone number the "
                                "account was registered with.")
                })

            if not _phone_belongs_to_wallet(phone, client.get("wallet_address", "")):
                return jsonify({
                    "success": False,
                    "message": ("This number is tied to a different customer "
                                "account. Please use the phone number the "
                                "account was registered with.")
                })

            session["verified_phone"] = typed_phone
            session["verified_wallet"] = client.get("wallet_address", "")

            try:
                _grant_daily_visit_bonus(client.get("wallet_address", ""))
            except Exception as _vb_e:
                print(f"[PSC VISIT-BONUS] client/lookup failed: {_vb_e}")

            wallet = get_wallet(client["wallet_address"])
            balance = round(wallet["balance"], 2) if wallet else 0

            return jsonify({
                "success": True,
                "returning": True,
                "wallet": client["wallet_address"],
                "balance": balance,
                "wallet_psc": wallet.get("wallet_psc", 0) if wallet else 0,
                "bonus_psc": wallet.get("bonus_psc", 0) if wallet else 0,
                "savings_psc": wallet.get("savings_psc", 0) if wallet else 0,
                "deposit_psc": wallet.get("deposit_psc", 0) if wallet else 0,
                "daily_login_bonus_psc": wallet.get("daily_login_bonus_psc", 0) if wallet else 0,
                "details": {
                    "name": client.get("name", ""),
                    "phone": client.get("phone", phone),
                    "email": client.get("email", ""),
                    "address": client.get("address", ""),
                    "city": client.get("city", ""),
                    "landmark": client.get("landmark", ""),
                },
                "message": f"Welcome back, {client.get('name', '')}!"
            })

        wallet = create_client_wallet()
        upsert_client(phone, shipping, wallet["address"])

        session["verified_phone"] = _normalize_phone(phone)
        session["verified_wallet"] = wallet["address"]

        return jsonify({
            "success": True,
            "returning": False,
            "wallet": wallet["address"],
            "balance": wallet["balance"],
            "wallet_psc": wallet["wallet_psc"],
            "bonus_psc": wallet["bonus_psc"],
            "savings_psc": wallet.get("savings_psc", 0),
            "deposit_psc": wallet.get("deposit_psc", 0),
            "daily_login_bonus_psc": wallet.get("daily_login_bonus_psc", 0),
            "bonus": WELCOME_BONUS,
            "message": f"Welcome! You received {WELCOME_BONUS} bonus PSC."
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/checkout_validate", methods=["POST"])
def api_checkout_validate():
    try:
        data = request.get_json() or {}
        wallet_addr = str(data.get("wallet") or "").strip()
        raw_items = data.get("items") or []
        phone = str(data.get("phone") or "").strip()
        source = str(data.get("source") or "bonus").strip().lower()
        if source not in ("savings", "bonus", "auto"):
            source = "bonus"
        if source == "auto":
            source = "bonus"

        logged_in_user = session.get("user")
        if not logged_in_user:
            return jsonify({"success": False,
                            "message": "Please log in first before checking out."}), 401

        session_phone = _normalize_phone(logged_in_user.get("phone", ""))
        typed_phone = _normalize_phone(phone)
        if not session_phone or not typed_phone:
            return jsonify({"success": False,
                            "message": "Phone number is required."}), 400
        if session_phone != typed_phone:
            return jsonify({"success": False,
                            "message": "You are logged in with a different phone number."}), 403

        session_wallet = session.get("wallet", "")
        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False,
                            "message": "Wallet does not match the logged-in account."}), 403

        client = get_client_by_phone(phone)
        if not client:
            return jsonify({"success": False,
                            "message": "This phone number is not registered on any account."}), 404
        if str(client.get("wallet_address", "")).strip() != wallet_addr:
            return jsonify({"success": False,
                            "message": "This phone number does not belong to this wallet."}), 403

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        if not raw_items:
            return jsonify({"success": False, "message": "Cart is empty."}), 400

        gross_total_psc = 0.0
        total_client_kes = 0.0
        for ri in raw_items:
            try:
                pid = int(ri.get("product_id") or ri.get("id") or 0)
            except (TypeError, ValueError):
                pid = 0
            try:
                qty = int(ri.get("quantity", 1))
            except (TypeError, ValueError):
                qty = 1
            if qty < 1:
                qty = 1
            product = _PRODUCT_CACHE.get(pid)
            if not product:
                return jsonify({"success": False,
                                "message": "Product " + str(pid) + " not found."}), 404
            gross_total_psc += float(product["price"]) * qty
            total_client_kes += float(product.get("client_kes", product["kes_price"])) * qty

        gross_total_psc = round(gross_total_psc, 2)
        total_client_kes = round(total_client_kes, 2)

        (discount_kes, discount_psc, _u, _w) = calculate_bonus_discount(
            total_client_kes, wallet.get("bonus_psc", 0))
        payable_psc = round(max(0.0, gross_total_psc - discount_psc), 2)
        payable_kes = round(total_client_kes - discount_kes, 2)

        bonus_available = round(float(wallet.get("bonus_psc", 0) or 0), 2)
        purchased_available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
        savings_available = round(float(wallet.get("savings_psc", 0) or 0), 2)
        if source == "savings":
            source_available = savings_available
            source_label = "Savings"
        elif source == "bonus":
            source_available = bonus_available
            source_label = "Bonus"
        else:
            source_available = purchased_available
            source_label = "Purchased"

        if source_available <= 0:
            return jsonify({
                "success": False,
                "decline": True,
                "message": (f"You have no {source_label} PSC in your wallet. "
                            "Please top up before ordering."),
                "source": source,
                "payable_psc": payable_psc,
                "payable_kes": payable_kes,
                "bonus_available_psc": bonus_available,
                "purchased_psc": purchased_available,
                "savings_psc": savings_available,
                "psc_to_kes_rate": PSC_TO_KES_RATE,
            }), 402

        if source_available < payable_psc:
            shortfall = round(payable_psc - source_available, 2)

            if source == "bonus":
                return jsonify({
                    "success": False,
                    "decline": True,
                    "message": ("Your Bonus balance is " +
                                format(source_available, ".2f") +
                                " PSC, but this order needs " +
                                format(payable_psc, ".2f") +
                                " PSC. Please top up or pay from Savings."),
                    "source": "bonus",
                    "payable_psc": payable_psc,
                    "payable_kes": payable_kes,
                    "bonus_available_psc": bonus_available,
                    "purchased_psc": purchased_available,
                    "savings_psc": savings_available,
                    "psc_to_kes_rate": PSC_TO_KES_RATE,
                }), 402

            return jsonify({
                "success": False,
                "requires_top_up": True,
                "message": ("Your Savings balance is " + format(source_available, ".2f") +
                            " PSC, but this order needs " + format(payable_psc, ".2f") +
                            " PSC. Shortfall: " + format(shortfall, ".2f") +
                            " PSC (KES " + format(shortfall * PSC_TO_KES_RATE, ".2f") + ")."),
                "source": "savings",
                "gross_psc": gross_total_psc,
                "gross_kes": total_client_kes,
                "bonus_discount_psc": discount_psc,
                "bonus_discount_kes": discount_kes,
                "payable_psc": payable_psc,
                "payable_kes": payable_kes,
                "bonus_available_psc": bonus_available,
                "purchased_psc": purchased_available,
                "shortfall_psc": shortfall,
                "shortfall_kes": round(shortfall * PSC_TO_KES_RATE, 2),
                "psc_to_kes_rate": PSC_TO_KES_RATE,
            }), 402

        return jsonify({
            "success": True,
            "message": "Balance verified. You can proceed to confirm.",
            "source": source,
            "gross_psc": gross_total_psc,
            "gross_kes": total_client_kes,
            "bonus_discount_psc": discount_psc,
            "bonus_discount_kes": discount_kes,
            "payable_psc": payable_psc,
            "payable_kes": payable_kes,
            "bonus_available_psc": bonus_available,
            "purchased_psc": purchased_available,
            "savings_psc": savings_available,
            "psc_to_kes_rate": PSC_TO_KES_RATE,
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/checkout_partial_pay", methods=["POST"])
def api_checkout_partial_pay():
    try:
        data = request.get_json() or {}
        wallet_addr = str(data.get("wallet") or "").strip()
        raw_items = data.get("items") or []
        phone = str(data.get("phone") or "").strip()
        source = str(data.get("source") or "bonus").strip().lower()
        if source not in ("savings", "bonus"):
            source = "bonus"

        logged_in_user = session.get("user")
        if not logged_in_user:
            return jsonify({"success": False,
                            "message": "Please log in first before checking out."}), 401

        session_phone = _normalize_phone(logged_in_user.get("phone", ""))
        typed_phone = _normalize_phone(phone)
        if not session_phone or not typed_phone or session_phone != typed_phone:
            return jsonify({"success": False,
                            "message": "Phone number does not match your session."}), 403

        session_wallet = session.get("wallet", "")
        if not wallet_addr or (session_wallet and wallet_addr != session_wallet):
            return jsonify({"success": False,
                            "message": "Wallet does not match the logged-in account."}), 403

        client = get_client_by_phone(phone)
        if not client or str(client.get("wallet_address", "")).strip() != wallet_addr:
            return jsonify({"success": False,
                            "message": "This phone number does not belong to this wallet."}), 403

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        if not raw_items:
            return jsonify({"success": False, "message": "Cart is empty."}), 400

        gross_total_psc = 0.0
        total_client_kes = 0.0
        for ri in raw_items:
            try:
                pid = int(ri.get("product_id") or ri.get("id") or 0)
            except (TypeError, ValueError):
                pid = 0
            try:
                qty = int(ri.get("quantity", 1))
            except (TypeError, ValueError):
                qty = 1
            if qty < 1:
                qty = 1
            product = _PRODUCT_CACHE.get(pid)
            if not product:
                return jsonify({"success": False,
                                "message": "Product " + str(pid) + " not found."}), 404
            gross_total_psc += float(product["price"]) * qty
            total_client_kes += float(product.get("client_kes", product["kes_price"])) * qty

        gross_total_psc = round(gross_total_psc, 2)
        total_client_kes = round(total_client_kes, 2)

        (discount_kes, discount_psc, _u, _w) = calculate_bonus_discount(
            total_client_kes, wallet.get("bonus_psc", 0))
        payable_psc = round(max(0.0, gross_total_psc - discount_psc), 2)
        payable_kes = round(total_client_kes - discount_kes, 2)

        result = partial_deduct_for_shortfall(wallet_addr, payable_psc, source=source)
        if not result.get("ok"):
            return jsonify({
                "success": False,
                "decline": result.get("decline", False),
                "message": result.get("message", "Could not process partial payment."),
                "source": source,
                "payable_psc": payable_psc,
                "payable_kes": payable_kes,
                "psc_to_kes_rate": PSC_TO_KES_RATE,
            }), 402

        partial_id = "PP-" + uuid.uuid4().hex[:12]
        _admin_ledger_add({
            "type": "PARTIAL_CHECKOUT_PAYMENT",
            "partial_id": partial_id,
            "wallet_address": wallet_addr,
            "phone": phone,
            "source": source,
            "gross_psc": gross_total_psc,
            "gross_kes": total_client_kes,
            "payable_psc": payable_psc,
            "payable_kes": payable_kes,
            "paid_psc": result["paid_psc"],
            "paid_kes": result["paid_kes"],
            "remaining_psc": result["remaining_psc"],
            "remaining_kes": result["remaining_kes"],
            "items": raw_items,
            "status": "AWAITING_TOPUP",
            "time": _now(),
        })

        return jsonify({
            "success": True,
            "partial_id": partial_id,
            "source": source,
            "gross_psc": gross_total_psc,
            "gross_kes": total_client_kes,
            "bonus_discount_psc": discount_psc,
            "bonus_discount_kes": discount_kes,
            "payable_psc": payable_psc,
            "payable_kes": payable_kes,
            "paid_psc": result["paid_psc"],
            "paid_kes": result["paid_kes"],
            "remaining_psc": result["remaining_psc"],
            "remaining_kes": result["remaining_kes"],
            "wallet_psc_after": result["wallet_psc_after"],
            "bonus_psc_after": result["bonus_psc_after"],
            "savings_psc_after": result.get("savings_psc_after", 0.0),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": ("Paid " + format(result["paid_psc"], ".2f") + " PSC "
                        "(KES " + format(result["paid_kes"], ".2f") + ") from your " +
                        ("Savings" if source == "savings" else "Bonus") + ". "
                        "Remaining: " + format(result["remaining_psc"], ".2f") + " PSC "
                        "(KES " + format(result["remaining_kes"], ".2f") + ")."),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


def calculate_checkout_payment(wallet, gross_psc, total_client_kes, payment_source="auto"):
    gross_psc = round(float(gross_psc), 2)
    total_client_kes = round(float(total_client_kes), 2)

    payment_source = str(payment_source or "auto").strip().lower()
    if payment_source not in ("savings", "bonus", "auto"):
        payment_source = "auto"
    if payment_source == "auto":
        payment_source = "bonus"

    bonus_available = round(float(wallet.get("bonus_psc", 0) or 0), 2)
    purchased_available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
    savings_available = round(float(wallet.get("savings_psc", 0) or 0), 2)
    deposit_available = round(float(wallet.get("deposit_psc", 0) or 0), 2)

    (
        discount_kes,
        discount_psc,
        bonus_discount_used_psc,
        _wallet_funded_psc,
    ) = calculate_bonus_discount(total_client_kes, bonus_available)

    payable_psc = round(max(0.0, gross_psc - discount_psc), 2)
    payable_kes = round(max(0.0, total_client_kes - discount_kes), 2)

    if payment_source == "savings":
        source_available = savings_available
        source_label = "Savings"
    elif payment_source == "bonus":
        source_available = bonus_available
        source_label = "Bonus"
    else:
        source_available = purchased_available
        source_label = "Purchased"

    base = {
        "gross_psc": gross_psc,
        "gross_kes": total_client_kes,
        "bonus_discount_kes": discount_kes,
        "bonus_discount_psc": discount_psc,
        "bonus_discount_used_psc": bonus_discount_used_psc,
        "payable_psc": payable_psc,
        "payable_kes": payable_kes,
        "purchased_psc_available": purchased_available,
        "bonus_psc_available": bonus_available,
        "savings_psc_available": savings_available,
        "deposit_psc_available": deposit_available,
        "purchased_psc_used": 0.0,
        "savings_psc_used": 0.0,
        "bonus_psc_used": 0.0,
        "bonus_payment_psc": 0.0,
        "total_psc_used": 0.0,
        "payment_source": payment_source,
        "min_balance_to_shop": MIN_BALANCE_TO_SHOP,
    }

    if source_available < MIN_BALANCE_TO_SHOP - 1e-9:
        base.update({
            "ok": False,
            "decline": True,
            "message": (
                f"A minimum of {MIN_BALANCE_TO_SHOP:.2f} PSC must be in your "
                f"{source_label} balance to shop. You have {source_available:.2f} PSC."
            ),
            "top_up_psc": round(max(0.0, MIN_BALANCE_TO_SHOP - source_available), 2),
            "top_up_kes": round(
                max(0.0, MIN_BALANCE_TO_SHOP - source_available) * PSC_TO_KES_RATE, 2
            ),
        })
        return base

    if payable_psc <= 0:
        base.update({
            "ok": True,
            "top_up_psc": 0.0,
            "top_up_kes": 0.0,
        })
        return base

    if source_available + 1e-9 < payable_psc:
        shortfall = round(payable_psc - source_available, 2)
        base.update({
            "ok": False,
            "requires_top_up": True,
            "message": (
                f"Your {source_label} balance is {source_available:.2f} PSC, "
                f"but this order needs {payable_psc:.2f} PSC after the Bonus discount. "
                f"Shortfall: {shortfall:.2f} PSC "
                f"(KES {shortfall * PSC_TO_KES_RATE:.2f}). "
                f"Please top up your {source_label.lower()} balance before checking out."
            ),
            "top_up_psc": shortfall,
            "top_up_kes": round(shortfall * PSC_TO_KES_RATE, 2),
        })
        return base

    if payment_source == "savings":
        base["savings_psc_used"] = payable_psc
    else:
        base["purchased_psc_used"] = payable_psc

    base["total_psc_used"] = payable_psc
    base["ok"] = True
    base["top_up_psc"] = 0.0
    base["top_up_kes"] = 0.0
    return base


_CHECKOUT_PAYMENT_LOCK = threading.RLock()


def apply_checkout_payment(wallet_addr, payment):
    if not payment.get("ok"):
        return False, payment.get("message", "Checkout payment failed.")

    src = str(payment.get("payment_source", "bonus")).strip().lower()
    amount = round(float(payment.get("total_psc_used", 0) or 0), 2)
    if amount <= 0:
        return True, "OK"

    with _CHECKOUT_PAYMENT_LOCK:
        if src == "savings":
            return deduct_savings_psc(wallet_addr, amount)
        if src == "bonus":
            return deduct_bonus_psc(wallet_addr, amount)
        return deduct_wallet_psc(wallet_addr, amount)


def rollback_checkout_payment(wallet_addr, payment):
    if not payment or not payment.get("ok"):
        return False

    amount = round(float(payment.get("total_psc_used", 0) or 0), 2)
    if amount <= 0:
        return True

    wallet = get_wallet(wallet_addr)
    if not wallet:
        return False

    src = str(payment.get("payment_source", "bonus")).strip().lower()
    if src == "savings":
        wallet["savings_psc"] = round(
            float(wallet.get("savings_psc", 0) or 0) + amount, 2
        )
    elif src == "bonus":
        wallet["bonus_psc"] = round(
            float(wallet.get("bonus_psc", 0) or 0) + amount, 2
        )
    else:
        wallet["wallet_psc"] = round(
            float(wallet.get("wallet_psc", 0) or 0) + amount, 2
        )

    wallet["balance"] = _wallet_total(wallet)
    _save_wallet(wallet)
    _admin_merge_wallet(
        address=wallet_addr,
        purchased_psc=wallet.get("wallet_psc", 0),
        bonus_psc=wallet.get("bonus_psc", 0),
        savings_psc=wallet.get("savings_psc", 0),
        deposit_psc=wallet.get("deposit_psc", 0),
    )
    return True


@app.route("/api/checkout_preview", methods=["POST"])
def api_checkout_preview():
    try:
        data = request.get_json() or {}
        wallet_addr = data.get("wallet", "")
        payment_source = str(
            data.get("source") or data.get("payment_source") or "bonus"
        ).strip().lower()
        if payment_source not in ("savings", "bonus", "auto"):
            payment_source = "bonus"

        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."})

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"})

        raw_items = data.get("items") or []

        if not raw_items:
            try:
                product_id = int(data.get("product_id", 0))
            except (TypeError, ValueError):
                product_id = 0

            try:
                quantity = int(data.get("quantity", 1))
            except (TypeError, ValueError):
                quantity = 1

            if quantity < 1:
                quantity = 1

            product = _PRODUCT_CACHE.get(product_id)
            if not product:
                return jsonify({"success": False, "message": "Product not found."})

            raw_items = [{"product_id": product_id, "quantity": quantity}]

        gross_psc = 0.0
        gross_kes = 0.0

        for ri in raw_items:
            try:
                pid = int(ri.get("product_id") or ri.get("id") or 0)
            except (TypeError, ValueError):
                pid = 0

            try:
                qty = int(ri.get("quantity", 1))
            except (TypeError, ValueError):
                qty = 1

            if qty < 1:
                qty = 1

            product = _PRODUCT_CACHE.get(pid)
            if not product:
                return jsonify({"success": False,
                                "message": f"Product {pid} not found."})

            gross_psc += float(product["price"]) * qty
            gross_kes += float(product.get("client_kes", product["kes_price"])) * qty

        gross_psc = round(gross_psc, 2)
        gross_kes = round(gross_kes, 2)

        payment = calculate_checkout_payment(
            wallet, gross_psc, gross_kes, payment_source
        )

        if not payment["ok"]:
            return jsonify({
                "success": False,
                "message": payment["message"],
                "source": payment.get("payment_source", payment_source),
                "gross_psc": gross_psc,
                "gross_kes": gross_kes,
                "wallet_psc": wallet.get("wallet_psc", 0),
                "bonus_psc": wallet.get("bonus_psc", 0),
                "savings_psc": wallet.get("savings_psc", 0),
                "purchased_psc_available": payment.get(
                    "purchased_psc_available",
                    wallet.get("wallet_psc", 0)
                ),
                "purchased_psc_used": payment.get("purchased_psc_used", 0),
                "top_up_psc": payment.get("top_up_psc", 0),
                "top_up_kes": payment.get("top_up_kes", 0),
                "requires_top_up": payment.get("requires_top_up", False),
                "decline": payment.get("decline", False),
                "min_balance_to_shop": MIN_BALANCE_TO_SHOP,
                "psc_to_kes_rate": PSC_TO_KES_RATE,
            })

        return jsonify({
            "success": True,
            "source": payment.get("payment_source", payment_source),
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "gross_psc": payment["gross_psc"],
            "gross_kes": payment["gross_kes"],
            "bonus_discount_psc": payment["bonus_discount_psc"],
            "bonus_discount_kes": payment["bonus_discount_kes"],
            "bonus_discount_rate": BONUS_DISCOUNT_RATE,
            "payable_psc": payment["payable_psc"],
            "payable_kes": payment["payable_kes"],
            "purchased_psc_used": payment["purchased_psc_used"],
            "bonus_psc_used": payment["bonus_psc_used"],
            "savings_psc_used": payment.get("savings_psc_used", 0.0),
            "wallet_psc": wallet.get("wallet_psc", 0),
            "bonus_psc": wallet.get("bonus_psc", 0),
            "savings_psc": wallet.get("savings_psc", 0),
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/order_form")
def order_form():
    product_id = request.args.get("product_id", type=int)
    wallet = request.args.get("wallet", "")
    product = _PRODUCT_CACHE.get(product_id)

    if not product:
        products = load_products("electronics")
        product = _PRODUCT_CACHE.get(product_id)

    if not product:
        return redirect(url_for("index"))

    w = get_wallet(wallet) if wallet else None
    balance = round(w["balance"], 2) if w else 0

    return render_template(
        "order_form.html",
        product=_strip_vendor_fields(product),
        wallet=wallet,
        balance=balance,
    )


@app.route("/api/place_order", methods=["POST"])
def api_place_order():
    try:
        data = request.get_json() or {}
        wallet_addr = data.get("wallet", "")
        try:
            product_id = int(data.get("product_id", 0))
            quantity = int(data.get("quantity", 1))
        except (TypeError, ValueError):
            return jsonify({"success": False, "message": "Invalid product or quantity."}), 400

        if product_id <= 0:
            return jsonify({"success": False, "message": "Product is required."}), 400
        if quantity < 1:
            return jsonify({"success": False, "message": "Quantity must be at least 1."}), 400
        shipping = data.get("shipping", {}) or {}

        _phone_from_order = str(
            data.get("phone") or shipping.get("phone") or ""
        ).strip()

        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."})

        if not _phone_from_order:
            return jsonify({"success": False,
                            "message": "Phone number is required."})

        _client_for_order = get_client_by_phone(_phone_from_order)
        if not _client_for_order:
            return jsonify({"success": False,
                            "message": "This phone number is not registered on any account."})

        _stored_wallet = str(_client_for_order.get("wallet_address", "")).strip()
        if not _stored_wallet or _stored_wallet != str(wallet_addr).strip():
            return jsonify({"success": False,
                            "message": "This phone number does not belong to the wallet being charged."})

        _session_phone = session.get("verified_phone")
        _session_wallet = session.get("verified_wallet")
        if not _session_phone or not _session_wallet:
            return jsonify({"success": False,
                            "message": "Please verify your phone number at checkout before paying."})
        if _normalize_phone(_session_phone) != _normalize_phone(_phone_from_order):
            return jsonify({"success": False,
                            "message": "Your session was verified with a different phone number."})
        if str(_session_wallet).strip() != str(wallet_addr).strip():
            return jsonify({"success": False,
                            "message": "Your session was verified with a different wallet."})

        product = _PRODUCT_CACHE.get(product_id)
        if not product:
            return jsonify({"success": False, "message": "Product not found."})

        gross_total_psc = round(product["price"] * quantity, 2)
        total_client_kes = round(product.get("client_kes", product["kes_price"]) * quantity, 2)

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"})

        payment = calculate_checkout_payment(wallet, gross_total_psc, total_client_kes, shipping.get("payment_preference", "auto"))
        if not payment["ok"]:
            return jsonify({"success": False, "message": payment["message"]})

        ok, msg = apply_checkout_payment(wallet_addr, payment)
        if not ok:
            return jsonify({"success": False, "message": msg})

        total_psc = payment["payable_psc"]
        orders = _load_orders()

        product_snapshot = {
            "id": product["id"],
            "name": product["name"],
            "price": product["price"],
            "kes_price": product["kes_price"],
            "client_kes": product.get("client_kes", product["kes_price"]),
            "quantity": quantity,
            "category": product.get("category", ""),
            "source": product.get("source", ""),
            "vendor": product.get("vendor", ""),
            "image": product.get("image", ""),
            "markup": product.get("markup", MARKUP_DEFAULT),
            "save_more": product.get("save_more", False),
        }

        order = {
            "order_id": _next_order_id(orders),
            "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "client_wallet": wallet_addr,
            "items": [product_snapshot],
            "total_psc": total_psc,
            "gross_total_psc": payment["gross_psc"],
            "bonus_discount_psc": payment["bonus_discount_psc"],
            "bonus_discount_kes": payment["bonus_discount_kes"],
            "purchased_psc_used": payment["purchased_psc_used"],
            "savings_psc_used": payment.get("savings_psc_used", 0.0),
            "bonus_psc_used": payment["bonus_psc_used"],
            "gross_total_kes": payment["gross_kes"],
            "final_payable_kes": round(payment["payable_psc"] * PSC_TO_KES_RATE, 2),
            "shipping": shipping,
            "status": "NEW",
            "vendor_request_id": None,
        }

        orders.append(order)
        try:
            _save_orders(orders)
        except Exception:
            rollback_checkout_payment(wallet_addr, payment)
            raise
        upsert_client(shipping.get("phone", ""), shipping, wallet_addr)

        return jsonify({
            "success": True,
            "order_id": order["order_id"],
            "message": f"Order {order['order_id']} placed!",
            "gross_psc": payment["gross_psc"],
            "gross_kes": payment["gross_kes"],
            "bonus_discount_psc": payment["bonus_discount_psc"],
            "bonus_discount_kes": payment["bonus_discount_kes"],
            "payable_psc": payment["payable_psc"],
            "payable_kes": payment["payable_kes"],
            "purchased_psc_used": payment["purchased_psc_used"],
            "savings_psc_used": payment.get("savings_psc_used", 0.0),
            "bonus_psc_used": payment["bonus_psc_used"],
            "wallet_psc": wallet["wallet_psc"],
            "bonus_psc": wallet["bonus_psc"],
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/order_success")
def order_success():
    return render_template("order_success.html")


@app.route("/api/products")
def api_products():
    try:
        raw_q = request.args.get("q", "electronics")
        cat_key = request.args.get("category", "").strip()
        light = request.args.get("light", "") == "1"

        vendor_hint, _ = _extract_vendor_hint(raw_q)
        q = _normalize_search_query(raw_q)

        if cat_key:
            cat = next((c for c in CATEGORY_GROUPS if c["key"] == cat_key), None)
            if cat:
                q = cat["query"]
                vendor_hint = None

        products = load_products(q, vendor=vendor_hint)

        if not products and q and " " in q:
            broader = q.split()[0]
            if broader and broader.lower() != q.lower():
                print(f"[PSC SEARCH] '{q}' empty, retrying with '{broader}'")
                products = load_products(broader, vendor=None)

        _register_products(products)
        products = _tag_new(products)

        if light:
            products = products[:3]

        return jsonify({
            "success": True,
            "products": _strip_products_for_client(products),
            "count": len(products),
            "vendor": "all",
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "cached": True,
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/cache/clear", methods=["POST", "GET"])
def api_cache_clear():
    _cache_clear()
    with _CATEGORY_IMAGE_LOCK:
        _CATEGORY_IMAGE_CACHE.clear()
    try:
        _save_disk_cache(force=True)
    except Exception:
        pass
    return jsonify({"success": True, "message": "Cache cleared."})


@app.route("/api/cache/refresh", methods=["POST", "GET"])
def api_cache_refresh():
    started = []
    for cat in CATEGORY_GROUPS:
        cache_key = f"products::all::{cat['query'].lower()}"
        try:
            _background_refresh_products(cat["query"], vendor=None, cache_key=cache_key)
            started.append(cat["key"])
        except Exception as e:
            print(f"[PSC REFRESH] start failed for {cat['key']}: {e}")
    return jsonify({
        "success": True,
        "message": f"Background refresh started for {len(started)} categories.",
        "categories": started,
    })


@app.route("/cart_checkout")
def cart_checkout():
    wallet = request.args.get("wallet", "")
    w = get_wallet(wallet) if wallet else None
    balance = round(w["balance"], 2) if w else 0

    return render_template(
        "cart_checkout.html",
        wallet=wallet,
        balance=balance,
    )


@app.route("/api/place_multi_order", methods=["POST"])
def api_place_multi_order():
    try:
        data = request.get_json() or {}
        wallet_addr = data.get("wallet", "")
        raw_items = data.get("items", [])
        shipping = data.get("shipping", {}) or {}

        _phone_from_order = str(
            data.get("phone") or shipping.get("phone") or ""
        ).strip()

        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."})

        if not _phone_from_order:
            return jsonify({"success": False,
                            "message": "Phone number is required to verify the account before payment."})

        _client_for_order = get_client_by_phone(_phone_from_order)
        if not _client_for_order:
            return jsonify({"success": False,
                            "message": "This phone number is not registered on any account."})

        _stored_wallet_for_order = str(_client_for_order.get("wallet_address", "")).strip()
        if not _stored_wallet_for_order or _stored_wallet_for_order != str(wallet_addr).strip():
            return jsonify({"success": False,
                            "message": "This phone number does not belong to the wallet being charged."})

        _stored_phone_for_order = _normalize_phone(_client_for_order.get("phone", ""))
        if (
                _stored_phone_for_order
                and _stored_phone_for_order != _normalize_phone(_phone_from_order)
        ):
            return jsonify({"success": False,
                            "message": "This phone number does not belong to the wallet being charged."})

        _session_phone = session.get("verified_phone")
        _session_wallet = session.get("verified_wallet")

        if not _session_phone or not _session_wallet:
            return jsonify({"success": False,
                            "message": "Please verify your phone number at checkout before paying."})

        if _normalize_phone(_session_phone) != _normalize_phone(_phone_from_order):
            return jsonify({"success": False,
                            "message": "Your session was verified with a different phone number."})

        if str(_session_wallet).strip() != str(wallet_addr).strip():
            return jsonify({"success": False,
                            "message": "Your session was verified with a different wallet."})

        if not raw_items:
            return jsonify({"success": False, "message": "Cart is empty"})

        items = []
        gross_total_psc = 0.0
        total_client_kes = 0.0

        for ri in raw_items:
            try:
                pid = int(ri.get("product_id") or ri.get("id") or 0)
                qty = int(ri.get("quantity", 1))
            except (TypeError, ValueError):
                return jsonify({"success": False, "message": "Invalid product or quantity in cart."}), 400

            if pid <= 0:
                return jsonify({"success": False, "message": "Invalid product in cart."}), 400
            if qty < 1:
                return jsonify({"success": False, "message": "Cart quantity must be at least 1."}), 400

            product = _PRODUCT_CACHE.get(pid)
            if not product:
                return jsonify({"success": False,
                                "message": f"Product {pid} not found."})

            sub = round(product["price"] * qty, 2)
            item_client_kes = round(product.get("client_kes", product["kes_price"]) * qty, 2)

            gross_total_psc += sub
            total_client_kes += item_client_kes

            items.append({
                "id": product["id"],
                "name": product["name"],
                "price": product["price"],
                "kes_price": product["kes_price"],
                "client_kes": product.get("client_kes", product["kes_price"]),
                "quantity": qty,
                "category": product.get("category", ""),
                "source": product.get("source", ""),
                "vendor": product.get("vendor", ""),
                "image": product.get("image", ""),
                "markup": product.get("markup", MARKUP_DEFAULT),
                "save_more": product.get("save_more", False),
            })

        gross_total_psc = round(gross_total_psc, 2)
        total_client_kes = round(total_client_kes, 2)

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"})

        payment = calculate_checkout_payment(wallet, gross_total_psc, total_client_kes, shipping.get("payment_preference", "auto"))
        if not payment["ok"]:
            return jsonify({"success": False, "message": payment["message"]})

        ok, msg = apply_checkout_payment(wallet_addr, payment)
        if not ok:
            return jsonify({"success": False, "message": msg})

        total_psc = payment["payable_psc"]
        orders = _load_orders()

        order = {
            "order_id": _next_order_id(orders),
            "created_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "client_wallet": wallet_addr,
            "items": items,
            "total_psc": total_psc,
            "gross_total_psc": payment["gross_psc"],
            "bonus_discount_psc": payment["bonus_discount_psc"],
            "bonus_discount_kes": payment["bonus_discount_kes"],
            "purchased_psc_used": payment["purchased_psc_used"],
            "savings_psc_used": payment.get("savings_psc_used", 0.0),
            "bonus_psc_used": payment["bonus_psc_used"],
            "gross_total_kes": payment["gross_kes"],
            "final_payable_kes": round(payment["payable_psc"] * PSC_TO_KES_RATE, 2),
            "shipping": shipping,
            "status": "NEW",
            "vendor_request_id": None,
        }

        orders.append(order)
        try:
            _save_orders(orders)
        except Exception:
            rollback_checkout_payment(wallet_addr, payment)
            raise
        upsert_client(shipping.get("phone", ""), shipping, wallet_addr)

        return jsonify({
            "success": True,
            "order_id": order["order_id"],
            "message": f"Order {order['order_id']} placed!",
            "gross_psc": payment["gross_psc"],
            "gross_kes": payment["gross_kes"],
            "bonus_discount_psc": payment["bonus_discount_psc"],
            "bonus_discount_kes": payment["bonus_discount_kes"],
            "payable_psc": payment["payable_psc"],
            "payable_kes": payment["payable_kes"],
            "purchased_psc_used": payment["purchased_psc_used"],
            "savings_psc_used": payment.get("savings_psc_used", 0.0),
            "bonus_psc_used": payment["bonus_psc_used"],
            "wallet_psc": wallet["wallet_psc"],
            "bonus_psc": wallet["bonus_psc"],
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# PAYMENTS GATEWAYS ENDPOINT (stub returning empty list)
# ============================================================

@app.route("/api/payments/gateways", methods=["GET"])
def api_payments_gateways():
    """Payment gateways have been disabled. Returns empty list."""
    return jsonify({
        "success": True,
        "gateways": [],
        "message": "Payment gateways are disabled. PSC can only be obtained via admin credit, P2P transfer, mining rewards, or bonus.",
    })


# ============================================================
# BLOCKCHAIN MINING + REAL-TIME WEBSOCKET
# ============================================================

try:
    from flask_socketio import SocketIO, emit as ws_emit, join_room, leave_room
    _SOCKETIO_AVAILABLE = True
except Exception as _sio_imp_err:
    print(f"[PSC WS] flask_socketio not installed ({_sio_imp_err}). "
          f"WebSocket push disabled; mining endpoints still active.")
    _SOCKETIO_AVAILABLE = False


MINING_REWARD_PSC       = float(os.getenv("MINING_REWARD_PSC", "0.5") or 0.5)
MINING_DIFFICULTY       = int(os.getenv("MINING_DIFFICULTY", "3") or 3)
MINING_MAX_DIFFICULTY   = int(os.getenv("MINING_MAX_DIFFICULTY", "5") or 5)
MINING_MAX_TX_PER_BLOCK = int(os.getenv("MINING_MAX_TX_PER_BLOCK", "50") or 50)

BLOCKCHAIN_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "blockchain.json"
)

_BLOCKCHAIN_LOCK = threading.Lock()


def _bc_compute_hash(block):
    payload = (
        str(block.get("index", 0))
        + "|" + str(block.get("timestamp", ""))
        + "|" + json.dumps(block.get("transactions") or [],
                           sort_keys=True, separators=(",", ":"))
        + "|" + str(block.get("previous_hash", ""))
        + "|" + str(block.get("nonce", 0))
        + "|" + str(block.get("miner", ""))
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _bc_genesis():
    g = {
        "index": 0,
        "timestamp": _now(),
        "transactions": [],
        "previous_hash": "0" * 64,
        "nonce": 0,
        "miner": "GENESIS",
        "reward_psc": 0.0,
        "difficulty": 0,
    }
    g["hash"] = _bc_compute_hash(g)
    return g


def _bc_load():
    d = _jload(BLOCKCHAIN_FILE, None)
    if not isinstance(d, dict) or not d.get("chain"):
        d = {"chain": [_bc_genesis()], "difficulty": MINING_DIFFICULTY}
        _jsave(BLOCKCHAIN_FILE, d)
    return d


def _bc_save(d):
    _jsave(BLOCKCHAIN_FILE, d)


def _bc_validate(chain):
    if not chain:
        return False, "empty chain"
    for i in range(1, len(chain)):
        blk = chain[i]
        prev = chain[i - 1]
        if blk.get("previous_hash") != prev.get("hash"):
            return False, f"block {i}: previous_hash mismatch"
        if _bc_compute_hash(blk) != blk.get("hash"):
            return False, f"block {i}: hash mismatch"
    return True, "OK"


def _bc_do_mine(miner_wallet, transactions, difficulty):
    try:
        difficulty = max(1, min(int(difficulty or MINING_DIFFICULTY),
                                MINING_MAX_DIFFICULTY))
    except (TypeError, ValueError):
        difficulty = MINING_DIFFICULTY

    with _BLOCKCHAIN_LOCK:
        d = _bc_load()
        chain = d["chain"]
        prev = chain[-1]
        block = {
            "index": len(chain),
            "timestamp": _now(),
            "transactions": transactions or [],
            "previous_hash": prev.get("hash", ""),
            "nonce": 0,
            "miner": miner_wallet or "",
            "reward_psc": float(MINING_REWARD_PSC) if miner_wallet else 0.0,
            "difficulty": difficulty,
        }
        target = "0" * difficulty
        attempts = 0
        t0 = time.time()
        while True:
            block["nonce"] = attempts
            h = _bc_compute_hash(block)
            if h.startswith(target):
                block["hash"] = h
                break
            attempts += 1
            if attempts > 10_000_000:
                return None, ("Mining timed out (difficulty too high; "
                              "try a lower difficulty).")
        block["attempts"] = attempts
        block["mined_in_seconds"] = round(time.time() - t0, 4)

        chain.append(block)
        d["chain"] = chain
        d["difficulty"] = difficulty
        _bc_save(d)
        return block, "OK"


def _bc_emit_new_block(block):
    if not _SOCKETIO_AVAILABLE:
        return
    try:
        socketio.emit("new_block", {
            "index": block.get("index"),
            "hash": block.get("hash"),
            "miner": block.get("miner"),
            "tx_count": len(block.get("transactions") or []),
            "nonce": block.get("nonce"),
            "difficulty": block.get("difficulty"),
            "reward_psc": block.get("reward_psc", 0.0),
            "time": block.get("timestamp"),
        }, broadcast=True)
        if block.get("miner"):
            socketio.emit("my_block", {
                "index": block.get("index"),
                "hash": block.get("hash"),
                "reward_psc": block.get("reward_psc", 0.0),
                "nonce": block.get("nonce"),
                "time": block.get("timestamp"),
            }, room="wallet:" + str(block["miner"]))
    except Exception as e:
        print(f"[PSC WS] new_block emit failed: {e}")


def _bc_credit_reward(miner_wallet, block_index, tag="MINING_REWARD"):
    if not miner_wallet or MINING_REWARD_PSC <= 0:
        return ""
    w = get_wallet(miner_wallet)
    if not w:
        return " (miner wallet not found; reward skipped)"
    try:
        _add_psc_to_target(
            miner_wallet, MINING_REWARD_PSC,
            target="spendable",
            kes_amount=round(MINING_REWARD_PSC * PSC_TO_KES_RATE, 2),
            payment_reference=f"{tag}:{block_index}",
            audit_type=tag,
        )
        return f" Credited {MINING_REWARD_PSC:.2f} PSC mining reward."
    except Exception as e:
        print(f"[PSC MINING] reward credit failed: {e}")
        return " (reward credit failed)"


def _bc_extract_miner(payload):
    return str(
        (payload or {}).get("wallet")
        or (payload or {}).get("miner")
        or request.args.get("wallet")
        or request.args.get("miner")
        or session.get("wallet", "")
        or ""
    ).strip()


@app.route("/api/mine", methods=["POST", "GET"])
def api_mine():
    try:
        data = request.get_json(silent=True) or {}
        miner = _bc_extract_miner(data)

        transactions = data.get("transactions") or []
        if not isinstance(transactions, list):
            transactions = []
        transactions = transactions[:MINING_MAX_TX_PER_BLOCK]

        raw_diff = data.get("difficulty")
        if raw_diff is None:
            raw_diff = request.args.get("difficulty")
        try:
            difficulty = int(raw_diff) if raw_diff is not None else MINING_DIFFICULTY
        except (TypeError, ValueError):
            difficulty = MINING_DIFFICULTY

        block, msg = _bc_do_mine(miner, transactions, difficulty)
        if not block:
            return jsonify({"success": False, "message": msg}), 500

        reward_msg = _bc_credit_reward(miner, block["index"], "MINING_REWARD")
        _bc_emit_new_block(block)

        return jsonify({
            "success": True,
            "message": (f"Mined block #{block['index']} with "
                        f"{len(transactions)} tx.{reward_msg}").strip(),
            "block": {
                "index":            block["index"],
                "hash":             block["hash"],
                "previous_hash":    block["previous_hash"],
                "nonce":            block["nonce"],
                "miner":            block["miner"],
                "transactions":     len(block["transactions"]),
                "difficulty":       block["difficulty"],
                "attempts":         block.get("attempts", 0),
                "mined_in_seconds": block.get("mined_in_seconds", 0),
                "reward_psc":       block.get("reward_psc", 0.0),
                "timestamp":        block["timestamp"],
            },
            "chain_length": block["index"] + 1,
            "psc_to_kes_rate": PSC_TO_KES_RATE,
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/mine_empty", methods=["POST", "GET"])
def api_mine_empty():
    try:
        data = request.get_json(silent=True) or {}
        miner = _bc_extract_miner(data)

        raw_diff = data.get("difficulty") or request.args.get("difficulty")
        try:
            difficulty = int(raw_diff) if raw_diff is not None else MINING_DIFFICULTY
        except (TypeError, ValueError):
            difficulty = MINING_DIFFICULTY

        block, msg = _bc_do_mine(miner, [], difficulty)
        if not block:
            return jsonify({"success": False, "message": msg}), 500

        reward_msg = _bc_credit_reward(miner, block["index"], "MINING_REWARD_EMPTY")
        _bc_emit_new_block(block)

        return jsonify({
            "success": True,
            "message": (f"Mined EMPTY block #{block['index']}.{reward_msg}").strip(),
            "block": {
                "index":            block["index"],
                "hash":             block["hash"],
                "previous_hash":    block["previous_hash"],
                "nonce":            block["nonce"],
                "miner":            block["miner"],
                "difficulty":       block["difficulty"],
                "attempts":         block.get("attempts", 0),
                "mined_in_seconds": block.get("mined_in_seconds", 0),
                "reward_psc":       block.get("reward_psc", 0.0),
                "timestamp":        block["timestamp"],
            },
            "chain_length": block["index"] + 1,
            "psc_to_kes_rate": PSC_TO_KES_RATE,
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/blockchain", methods=["GET"])
def api_blockchain_get():
    with _BLOCKCHAIN_LOCK:
        d = _bc_load()
    chain = d.get("chain") or []
    full = request.args.get("full") == "1"
    return jsonify({
        "success":      True,
        "chain_length": len(chain),
        "difficulty":   d.get("difficulty", MINING_DIFFICULTY),
        "latest":       chain[-1] if chain else None,
        "chain":        chain if full else chain[-10:],
        "psc_to_kes_rate": PSC_TO_KES_RATE,
    })


@app.route("/api/blockchain/validate", methods=["GET"])
def api_blockchain_validate():
    with _BLOCKCHAIN_LOCK:
        d = _bc_load()
    ok, msg = _bc_validate(d.get("chain") or [])
    return jsonify({
        "success":      ok,
        "message":      msg,
        "chain_length": len(d.get("chain") or []),
    })


if _SOCKETIO_AVAILABLE:
    socketio = SocketIO(
        app,
        cors_allowed_origins="*",
        async_mode="threading",
        logger=False,
        engineio_logger=False,
    )

    @socketio.on("connect")
    def _ws_on_connect():
        try:
            ws_emit("connected", {
                "message": "PSC realtime connected",
                "time": _now(),
                "psc_to_kes_rate": PSC_TO_KES_RATE,
            })
        except Exception as e:
            print(f"[PSC WS] connect emit failed: {e}")

    @socketio.on("subscribe")
    def _ws_on_subscribe(data):
        try:
            wallet = str((data or {}).get("wallet") or "").strip()
            if not wallet:
                ws_emit("error", {"message": "wallet required"})
                return
            join_room("wallet:" + wallet)
            ws_emit("subscribed", {"wallet": wallet, "time": _now()})
        except Exception as e:
            print(f"[PSC WS] subscribe failed: {e}")

    @socketio.on("unsubscribe")
    def _ws_on_unsubscribe(data):
        try:
            wallet = str((data or {}).get("wallet") or "").strip()
            if wallet:
                leave_room("wallet:" + wallet)
                ws_emit("unsubscribed", {"wallet": wallet})
        except Exception:
            pass

    @socketio.on("ping_psc")
    def _ws_on_ping():
        ws_emit("pong_psc", {"time": _now()})

    @app.after_request
    def _ws_wallet_broadcast(response):
        try:
            path = request.path or ""
            if not (path.startswith("/api/wallet")
                    or path.startswith("/api/account")
                    or path.startswith("/api/checkout")
                    or path.startswith("/api/place")
                    or path.startswith("/api/mine")):
                return response
            if response.status_code >= 400:
                return response
            if not response.is_json:
                return response

            body = response.get_json(silent=True) or {}
            wallet = (
                body.get("wallet")
                or body.get("address")
                or body.get("wallet_address")
                or session.get("wallet", "")
            )
            wallet = str(wallet or "").strip()
            if not wallet:
                return response

            payload = {
                "wallet":   wallet,
                "endpoint": path,
                "time":     _now(),
                "success":  bool(body.get("success", True)),
            }
            for k in ("balance", "wallet_psc", "bonus_psc", "savings_psc",
                      "deposit_psc", "daily_login_bonus_psc",
                      "held_psc", "psc_to_kes_rate"):
                if k in body:
                    payload[k] = body[k]

            try:
                socketio.emit("wallet_update", payload, room="wallet:" + wallet)
            except Exception:
                pass
        except Exception:
            pass
        return response

    _original_app_run = app.run
    _psc_in_socketio_run = False

    def _socketio_app_run(*args, **kwargs):
        global _psc_in_socketio_run
        kwargs.pop("threaded", None)

        if _psc_in_socketio_run:
            kwargs.pop("allow_unsafe_werkzeug", None)
            return _original_app_run(*args, **kwargs)

        kwargs.setdefault("allow_unsafe_werkzeug", True)
        _psc_in_socketio_run = True
        try:
            return socketio.run(app, *args, **kwargs)
        finally:
            _psc_in_socketio_run = False

    app.run = _socketio_app_run


# ---------- CACHE WARMER ----------

def _warm_cache():
    time.sleep(60)
    while True:
        try:
            print(f"[PSC] Warming cache (all categories)...")

            _PRIO_KEYS = {"phones","tv","appliances","health",
                          "home","fashion","computing","gaming"}
            _prio = [c["query"] for c in CATEGORY_GROUPS if c["key"] in _PRIO_KEYS]
            _rest = [c["query"] for c in CATEGORY_GROUPS if c["key"] not in _PRIO_KEYS]
            PRIORITY_KEYWORDS = _prio + _rest

            for kw in PRIORITY_KEYWORDS:
                waited = 0
                while _recent_user_activity(within_seconds=15):
                    time.sleep(3)
                    waited += 3
                    if waited % 15 == 0:
                        print(f"[PSC] warmer waiting for user idle ({waited}s)")
                try:
                    load_products(kw)
                    print(f"[PSC] warmed (priority): {kw}")
                except Exception as e:
                    print(f"[PSC] warm failed for '{kw}': {e}")
                time.sleep(_jitter(1500, 2500) / 1000.0)

            load_products_multi(
                ["smart tv", "smartphone", "laptop", "headphones"],
                per_query=10
            )
            try:
                _save_disk_cache(force=True)
            except Exception:
                pass
            print(f"[PSC] Cache warmed. Sleeping 10 min.")
        except Exception as e:
            print(f"[PSC] Warm failed: {e}")
        time.sleep(600)


def _log_request_start():
    from flask import g
    g._start_ts = time.time()


@app.after_request
def _log_request_end(response):
    from flask import g
    try:
        dur = (time.time() - g._start_ts) * 1000
        print(f"[TIMING] {request.method} {request.path} -> {response.status_code} in {dur:.0f} ms")
    except Exception:
        pass
    return response


_BG_STARTED = False
_BG_STARTED_LOCK = threading.Lock()


def _start_background_threads_once():
    global _BG_STARTED
    with _BG_STARTED_LOCK:
        if _BG_STARTED:
            return
        _BG_STARTED = True
        try:
            _ensure_wallet_dir()
        except Exception as e:
            print(f"[PSC] wallet dir error: {e}")
        try:
            _load_disk_cache()
        except Exception as e:
            print(f"[PSC] disk cache load error: {e}")
        try:
            if os.environ.get("RENDER") or os.environ.get("PSC_DISABLE_WARMER") == "1":
                print("[PSC] Render detected or warmer disabled. Skipping cache warmer to prevent OOM.")
            else:
                threading.Thread(target=_warm_cache, daemon=True).start()
            threading.Thread(
                target=_midnight_bonus_loop,
                name="_midnight_bonus_loop",
                daemon=True
            ).start()
            print("[PSC] Background threads started (cache warmer + midnight bonus).")
        except Exception as e:
            print(f"[PSC] Failed to start background threads: {e}")


_start_background_threads_once()


# === PSC PATCH: VENDOR TRIM ===
def _scrape_vendors_sequential(query, vendor=None):
    q = str(query or "electronics").strip() or "electronics"
    vendor = str(vendor or "").strip().lower() or None
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
    }

    _all_res = []
    if vendor in (None, "jumia"):
        p = _scrape_jumia(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "kilimall"):
        p = _scrape_kilimall(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "carrefour"):
        p = _scrape_carrefour(q)
        if p: _all_res.extend(p)

    if vendor in (None, "jiji"):
        p = _scrape_jiji(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "fahavi"):
        p = _scrape_fahavi(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "textbookcentre"):
        p = _scrape_textbookcentre(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "naivas"):
        p = _scrape_naivas(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "vivo"):
        p = _scrape_vivo(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "copell"):
        p = _scrape_copell(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "masoko"):
        p = _scrape_masoko(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "hotpoint"):
        p = _scrape_hotpoint(q, headers)
        if p: _all_res.extend(p)
    if vendor in (None, "samsungstore"):
        p = _scrape_samsungstore(q, headers)
        if p: _all_res.extend(p)

    if _all_res:
        return _all_res

    try:
        with open("products.json", "r") as f:
            _fb = json.load(f)
        _fbp = (_fb or {}).get("products", []) or []
        if _fbp:
            return _fbp
    except Exception:
        pass
    return []

_SCRAPE_COOLDOWN_SECONDS = 60
print("[PSC PATCH] Vendor trim + 60s scrape cooldown applied.")



@app.route("/api/hero_categories")
def api_hero_categories():
    try:
        result = []
        for cat in CATEGORY_GROUPS:
            key = cat["key"]
            cached = _CATEGORY_IMAGE_CACHE.get(key)
            img = ""
            if cached:
                img = cached.get("image", "")
            else:
                img = FALLBACK_CATEGORY_IMAGES.get(key, "")
                products = _cache_get(f"products::all::{cat['query'].lower()}") or []
                if not products:
                    products = _cache_get_soft(f"products::all::{cat['query'].lower()}") or []
                for p in products:
                    if p.get("image"):
                        img = p["image"]
                        break
            result.append({"key": key, "label": cat["label"], "image": img})
        import random
        random.shuffle(result)
        return jsonify({"success": True, "categories": result[:8]})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500

if __name__ == "__main__":
    print("=" * 60)
    print("  PSC - Pulse Shopping Coin (Client Site)")
    print("  PAYMENT GATEWAYS: DISABLED (admin-manual only)")
    _port = int(os.environ.get("PORT", 5001))
    print(f"  Open: http://localhost:{_port}")
    print(f"  New clients receive {WELCOME_BONUS} PSC on first visit")
    print(f"  Admin phone for top-ups: {ADMIN_PHONE}")
    print(f"  Cache TTL: {CACHE_TTL_SECONDS} seconds (10-minute TTL)")
    print("  Product IDs: STABLE")
    print(f"  Daily bonus: {DAILY_LOGIN_BONUS_PSC} PSC (KES {DAILY_LOGIN_BONUS_KES})")
    print(f"  Discount rate: {BONUS_DISCOUNT_RATE * 100:.2f}% of the KES total")
    print(f"  Min balance to shop: {MIN_BALANCE_TO_SHOP} PSC (ENFORCED)")
    print(f"  Admin sync file: {ADMIN_CLIENT_WALLETS_FILE}")
    print(f"  Scrape cooldown: {_SCRAPE_COOLDOWN_SECONDS}s per query")
    print("  Category images: /api/category_images (single call)")
    print("  Vendor visibility: HIDDEN from client")
    print(f"  Disk cache: {DISK_CACHE_FILE}")
    print("  Daily VISIT bonus: ENABLED (idempotent per day)")
    print(f"  KYC required for payout: {'YES' if KYC_REQUIRED else 'NO'}")
    print(f"  Payout velocity: {PAYOUT_VELOCITY_MAX_PER_DAY}/day, {PAYOUT_VELOCITY_MAX_PER_WEEK}/week")
    print(f"  CBK report threshold: KES {CBK_REPORT_THRESHOLD_KES:,.2f}")
    print(f"  KRA WHT threshold:    KES {KRA_WHT_THRESHOLD_KES:,.2f}")
    print("  Payment gateways:     DISABLED (Flutterwave/Paystack/CoinGate/MoonPay removed)")
    print(f"  Wallet deposits:      admin-manual only")
    print(f"  Withdraw daily max:   KES {WALLET_WITHDRAW_DAILY_MAX_KES:.2f} (admin confirm)")
    print(f"  P2P transfers:        ENABLED")
    print(f"  Savings bucket:       {'ENABLED' if WALLET_SAVINGS_ENABLED else 'DISABLED'}")
    print(f"  Deposit PSC pocket:   {'ENABLED (hold-only)' if WALLET_DEPOSIT_POCKET_ENABLED else 'DISABLED'}")
    print(f"  Wallet UI manifest:   /api/wallet/ui/<wallet>")
    print(f"  Three-bucket:         wallet_psc | savings_psc | deposit_psc")
    print("  Fallback products:    ENABLED (no empty grids)")
    print("=" * 60)

    app.run(
        debug=False,
        host="0.0.0.0",
        port=_port,
        threaded=True,
        use_reloader=False
    )