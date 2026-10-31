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
        img_val = product.get("image")
        if not img_val or str(img_val).strip().lower() in ("null", "none", ""):
            cat_name = str(product.get("category", "")).lower()
            name_val = str(product.get("name", "")).lower()
            if any(k in cat_name or k in name_val for k in ["phone", "tablet", "ipad", "iphone", "samsung"]):
                product["image"] = "https://images.unsplash.com/photo-1511707171634-5f897ff02aa9?w=400"
            elif any(k in cat_name or k in name_val for k in ["tv", "audio", "speaker"]):
                product["image"] = "https://images.unsplash.com/photo-1593359677879-a4bb92f829d1?w=400"
            elif any(k in cat_name or k in name_val for k in ["laptop", "comput", "macbook", "tool"]):
                product["image"] = "https://images.unsplash.com/photo-1496181133206-80ce9b88a853?w=400"
            elif any(k in cat_name or k in name_val for k in ["home", "kitchen", "fridge"]):
                product["image"] = "https://images.unsplash.com/photo-1584622650111-993a426fbf0a?w=400"
            elif any(k in cat_name or k in name_val for k in ["beauty", "health", "cream"]):
                product["image"] = "https://images.unsplash.com/photo-1556228578-0d85b1a4d571?w=400"
            elif any(k in cat_name or k in name_val for k in ["shoe", "fashion", "clothes"]):
                product["image"] = "https://images.unsplash.com/photo-1542291026-7eec264c27ff?w=400"
            else:
                product["image"] = "https://images.unsplash.com/photo-1505740420928-5e560c06d30e?w=400"

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

    # Fast stop-on-first-success logic
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

    if vendor == "fahavi":
        p = _scrape_fahavi(q, headers)
        if p: return p
    if vendor == "textbookcentre":
        p = _scrape_textbookcentre(q, headers)
        if p: return p
    if vendor == "naivas":
        p = _scrape_naivas(q, headers)
        if p: return p
    if vendor == "vivo":
        p = _scrape_vivo(q, headers)
        if p: return p
    if vendor == "copell":
        p = _scrape_copell(q, headers)
        if p: return p
    if vendor == "masoko":
        p = _scrape_masoko(q, headers)
        if p: return p
    if vendor == "hotpoint":
        p = _scrape_hotpoint(q, headers)
        if p: return p
    if vendor == "samsungstore":
        p = _scrape_samsungstore(q, headers)
        if p: return p

    try:
        with open("products.json", "r") as f:
            _fb = json.load(f)
        _fbp = (_fb or {}).get("products", []) or []
        if _fbp:
            return _fbp
    except Exception:
        pass
    return []

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