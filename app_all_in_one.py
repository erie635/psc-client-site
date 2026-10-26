"""
PSC - Pulse Shopping Coin
Client-facing online shop with automatic PSC wallet creation + client registry.
+ Category grouping, login/register, account persistence.
+ Animated hero carousel.
+ In-memory caching for fast loads (10-min TTL).
+ Product sources: Jumia, Kilimall, Carrefour.
+ Bonus PSC is used only as discount. Purchased PSC is used only as payment.
+ Daily bonus (1 PSC) is granted at 00:00 server time via background thread.
+ Purchase requests are forwarded to the admin's client_wallet_ledger.json.
+ Daily VISIT bonus: 1 PSC granted to the redeemable bucket on the first
  visit of the day (no login required), via _grant_daily_visit_bonus().
+ Virtual Accounts (VA): KYC, VA issuance, VA webhook, credit reconciliation,
  idempotency, reversals, bank list, account-name resolution, VA inflow limits,
  AML/PEP/sanctions screening, CBK/KRA reporting, payout velocity checks.
+ Multi-gateway PSC top-up: Flutterwave (existing) + Paystack (additive).
  Front-end can choose gateway per request. Default gateway = flutterwave.
  Nothing about Flutterwave's existing behaviour changes.
+ Wallet upgrades (additive): unlimited deposits (bank/card/M-Pesa), P2P
  PSC transfers between users, high-value withdrawals up to KES 100,000/day
  per user with admin confirm flow. All logic additive; nothing above
  was modified.
+ Savings sub-balance (additive): users can park PSC in a dedicated savings
  bucket that is never touched by shopping, then move it back on demand.
  Includes a full UI manifest endpoint so the front-end can render
  Deposit / Send / Withdraw / Save / Move back actions uniformly.
+ THREE-BUCKET WALLET (Option C, additive): adds a hold-only deposit_psc
  pocket in addition to wallet_psc (spendable) and savings_psc (parked).
  Deposits can be routed to spendable / savings / deposit via a `target`
  field on /api/wallet/deposit/initiate. The shop only reads wallet_psc,
  so deposit_psc is never spent by shopping. New endpoints:
    /api/wallet/deposit/move_in   (spendable -> deposit_psc)
    /api/wallet/deposit/move_out  (deposit_psc -> spendable)
  Everything above is unchanged; deposit_psc is purely additive.

PRODUCTION-READY GAP FIXES (applied, minimal, additive):
+ GAP #1: MIN_BALANCE_TO_SHOP is now actually enforced at checkout.
+ GAP #2: CACHE_TTL_SECONDS now matches the documented 10-min TTL.
+ GAP #3: _fallback_products() is now used when live scraping yields nothing,
         so the shop never shows an empty grid.

ADDITIONAL BUG FIXES (this revision, minimal, additive):
+ FIX #A: Renamed the two-argument VA file-write helper from _va_save(path, data)
          to _va_write(path, data) so it no longer shadows the one-argument
          _va_save(dict) used at VA call sites. Prevents RecursionError on all
          VA endpoints once VA_ENABLED=1.
+ FIX #B: Removed unreachable dead code in api_wallet_deposit_initiate()
          after the inline Flutterwave/Paystack if/else (both branches return).
+ FIX #C: Named the original midnight-bonus background thread
          "_midnight_bonus_loop" so a future hardened/debug wrapper can
          detect it and will not spawn a duplicate.
+ FIX #D: Rewrote /api/category_images to be cache-first. On the fast path
          it reads _CATEGORY_IMAGE_CACHE / _PRODUCT_CACHE_DB and returns
          in milliseconds. On the slow path (cold cache) it schedules a
          background refresh via the existing _background_refresh_products()
          helper and returns the emoji placeholder immediately. Scrapers
          (load_jumia / load_kilimall / load_carrefour) are NOT modified;
          they still run to completion on daemon threads, still respect
          _SCRAPE_LOCK, and still write to the same disk cache. Result:
          user requests never wait for a scrape, and the shop keeps
          collecting new items from all three vendors in the background.
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




# ---------- SIMPLE IN-MEMORY CACHE ----------
_PRODUCT_CACHE_DB = {}
_CACHE_LOCK = threading.Lock()

# === FIX 4: hoisted so _register_products() can be called by the
# loaders before their original definition point. Values are identical. ===
_PRODUCT_CACHE = {}
_CATEGORY_CACHE = {}
# === END FIX 4 ===


def _cache_get(key):
    """Return fresh data, or None if stale/missing.
    Never deletes stale entries: _cache_get_soft serves them while a
    background SWR refresh runs."""
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
#  PSC â€” PERSISTENT DISK CACHE (ADDITIVE, NON-BREAKING)
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

# === ANTI-BLOCK: per-vendor backoff + UA rotation + jitter ===
# Kilimall-specific Cloudflare / rate-limit backoff. Mirrors the Jumia
# pattern so a block on one vendor does not stop the other two.
_KILIMALL_BLOCKED_UNTIL = 0.0
_KILIMALL_BLOCKED_LOCK = threading.Lock()
_KILIMALL_BACKOFF_SECONDS = 300

# Carrefour-specific backoff. Carrefour is the most forgiving of the
# three, but still rate-limits on bursts; this keeps a bad window from
# cascading.
_CARREFOUR_BLOCKED_UNTIL = 0.0
_CARREFOUR_BLOCKED_LOCK = threading.Lock()
_CARREFOUR_BACKOFF_SECONDS = 300

# === ADDITIVE: Jiji-specific backoff (mirrors the other three) ===
_JIJI_BLOCKED_UNTIL = 0.0
_JIJI_BLOCKED_LOCK = threading.Lock()
_JIJI_BACKOFF_SECONDS = 300
# === END ADDITIVE ===

# === ADDITIVE: fail-open multi-vendor product aggregation ===
# Each vendor is isolated. A slow/blocked vendor cannot prevent the other
# vendors from returning products. Existing vendor loaders, caches and
# fallback behaviour remain unchanged.
_VENDOR_SCRAPE_TIMEOUT_SECONDS = 90
_VENDOR_EXECUTOR_MAX_WORKERS = 4
# === END ADDITIVE ===

# Rotating user-agent pool. Fresh UA per scrape reduces fingerprint-based
# bans. All eight strings are real, current, and widely seen in the wild.
_USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:125.0) Gecko/20100101 Firefox/125.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_4) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Mobile Safari/537.36",
]


def _random_ua():
    return random.choice(_USER_AGENTS)


def _jitter(base_ms, spread_ms=2000):
    """Return a random wait between base_ms and base_ms+spread_ms."""
    return random.randint(int(base_ms), int(base_ms) + int(spread_ms))
# === END ANTI-BLOCK constants ===


# === ADDITIVE: optional proxy support (off by default) ===
# If PSC_PROXY_SERVER is unset, _playwright_proxy_config() returns None
# and every browser launch is 100% identical to before. If it IS set,
# all vendor scrapers route through the proxy so vendors see the proxy
# IP instead of this server's real IP.
#
# .env examples:
#   PSC_PROXY_SERVER=http://proxy.example.com:8080
#   PSC_PROXY_USERNAME=myuser
#   PSC_PROXY_PASSWORD=mypass
#
# Rotating proxy pools:
#   PSC_PROXY_SERVERS=http://p1:8080,http://p2:8080,http://p3:8080
#   (when set, one is picked at random per browser launch)
PSC_PROXY_SERVER   = os.getenv("PSC_PROXY_SERVER", "").strip()
PSC_PROXY_USERNAME = os.getenv("PSC_PROXY_USERNAME", "").strip()
PSC_PROXY_PASSWORD = os.getenv("PSC_PROXY_PASSWORD", "").strip()
PSC_PROXY_SERVERS  = [
    s.strip() for s in os.getenv("PSC_PROXY_SERVERS", "").split(",") if s.strip()
]


def _playwright_proxy_config():
    """
    Return a dict for Playwright's `proxy=` kwarg, or None if no proxy
    is configured. When None is returned, the caller falls back to the
    original launch signature, so behaviour is unchanged.
    """
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




# === ADDITIVE: STEALTH HELPERS (Jumia + Jiji anti-block) ===
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
# === END ADDITIVE: STEALTH HELPERS ===

def _launch_browser(p):
    """
    Centralised browser launch. Applies proxy config if present.
    ADDITIVE: extra stealth flags to reduce bot-detection surface.
    """
    kwargs = {
        "channel": "chrome",
        "headless": True,
        "args": [
            "--disable-blink-features=AutomationControlled",
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "--disable-gpu",
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
    return p.chromium.launch(**kwargs)
# === END ADDITIVE: optional proxy support ===


def _scrape_recently_done(query_key):
    with _LAST_SCRAPE_AT_LOCK:
        ts = _LAST_SCRAPE_AT.get(query_key)
    if ts is None:
        return False
    return (time.time() - ts) < _SCRAPE_COOLDOWN_SECONDS


def _mark_scrape_done(query_key):
    with _LAST_SCRAPE_AT_LOCK:
        _LAST_SCRAPE_AT[query_key] = time.time()


# ---------- VENDOR REGISTRY (INTERNAL USE ONLY) ----------
VENDORS = {
    "jumia": {
        "key": "jumia",
        "label": "Jumia",
        "prefix": "jumia:",
        "url_template": "https://www.jumia.co.ke/catalog/?q={query}",
    },
    "kilimall": {
        "key": "kilimall",
        "label": "Kilimall",
        "prefix": "kilimall:",
        "url_template": "https://www.kilimall.co.ke/search?q={query}",
    },
    "carrefour": {
        "key": "carrefour",
        "label": "Carrefour",
        "prefix": "carrefour:",
        "url_template": "https://www.carrefour.ke/mafken/en/search?keyword={query}",
    },
    # === ADDITIVE: Jiji Kenya ===
    "jiji": {
        "key": "jiji",
        "label": "Jiji",
        "prefix": "jiji:",
        "url_template": "https://jiji.co.ke/search?query={query}",
    },
    # === END ADDITIVE ===

    # === ADDITIVE: 5 EXTRA KENYAN VENDORS ===
    "fahavi": {
        "key": "fahavi",
        "label": "Fahavi Computers",
        "prefix": "fahavi:",
        "url_template": "https://fahavicomputers.co.ke/?s={query}&post_type=product",
    },
    "textbookcentre": {
        "key": "textbookcentre",
        "label": "Text Book Centre",
        "prefix": "tbc:",
        "url_template": "https://textbookcentre.com/catalogsearch/result/?q={query}",
    },
    "naivas": {
        "key": "naivas",
        "label": "Naivas",
        "prefix": "naivas:",
        "url_template": "https://naivas.co.ke/search?q={query}",
    },
    "vivo": {
        "key": "vivo",
        "label": "Vivo",
        "prefix": "vivo:",
        "url_template": "https://vivo.co.ke/catalogsearch/result/?q={query}",
    },
    "copell": {
        "key": "copell",
        "label": "Copell",
        "prefix": "copell:",
        "url_template": "https://copell.co.ke/?s={query}&post_type=product",
    },
    # === END ADDITIVE: 5 EXTRA KENYAN VENDORS ===

    # === ADDITIVE: MASOKO + HOTPOINT + SAMSUNG BRAND STORE ===
    "masoko": {
        "key": "masoko",
        "label": "Safaricom Masoko",
        "prefix": "masoko:",
        "url_template": "https://masoko.co.ke/search?q={query}",
    },
    "hotpoint": {
        "key": "hotpoint",
        "label": "Hotpoint Appliances",
        "prefix": "hotpoint:",
        "url_template": "https://hotpoint.co.ke/catalogsearch/result/?q={query}",
    },
    "samsungstore": {
        "key": "samsungstore",
        "label": "Samsung Brand Store",
        "prefix": "samsung:",
        "url_template": "https://samsungbrandstore.co.ke/catalogsearch/result/?q={query}",
    },
    # === END ADDITIVE ===
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


# ---------- VENDOR HIDING ----------
_VENDOR_FIELDS_TO_STRIP = ("vendor", "vendor_url", "source")

_CLIENT_PRODUCT_FIELDS = (
    "id", "name", "price", "kes_price", "client_kes",
    "category", "image", "markup", "save_more", "is_new",
)


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


# ---------- SEARCH QUERY NORMALIZATION ----------
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
CACHE_TTL_SECONDS = 600  # 10 minutes for in-memory product cache
ADMIN_PHONE = "0796208133"

WALLET_DIR = r"C:\Users\erick\Desktop\PSC_Coin_Complete\wallets"
ORDERS_FILE = r"C:\Users\erick\Desktop\PSC_Coin_Complete\orders_from_clients.json"
CLIENTS_FILE = r"C:\Users\erick\Desktop\PSC_Coin_Complete\client_registry.json"

ADMIN_CLIENT_WALLETS_FILE = r"C:\Users\erick\Desktop\PSC_Coin_Complete\client_wallets.json"
ADMIN_LEDGER_FILE = r"C:\Users\erick\Desktop\PSC_Coin_Complete\client_wallet_ledger.json"

PAYMENTS_FILE         = r"C:\Users\erick\Desktop\PSC_Coin_Complete\payments.json"
WITHDRAWAL_QUEUE_FILE = r"C:\Users\erick\Desktop\PSC_Coin_Complete\withdrawal_queue.json"
PAYOUT_AUDIT_FILE     = r"C:\Users\erick\Desktop\PSC_Coin_Complete\payout_audit.json"

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

        # ============================================================
        # ADDITIVE: FRIDGES / REFRIGERATORS / FREEZERS = 15%
        # ============================================================
        "fridge": 0.15, "fridges": 0.15,
        "refrigerator": 0.15, "refrigerators": 0.15,
        "freezer": 0.15, "freezers": 0.15,
        "deep freezer": 0.15, "deepfreezer": 0.15, "deep-freezer": 0.15,
        "fridge freezer": 0.15, "fridge-freezer": 0.15,
        "cooler": 0.15, "coolers": 0.15,
        "cold room": 0.15, "coldroom": 0.15,

        # ============================================================
        # ADDITIVE: BEAUTY / COSMETICS / HEALTH & BEAUTY = 15%
        # ============================================================
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

# === AUTO-SHARE PATCH (added) ===
import auto_share
auto_share.install(app, port=5001, auto_start=True)
# === END AUTO-SHARE PATCH ===

# === SESSION PERSISTENCE (ADDITIVE) ===
# Store sessions on disk so server restarts don't log everyone out.
from flask_session import Session
app.config["SESSION_TYPE"] = "filesystem"
app.config["SESSION_FILE_DIR"] = r"C:\Users\erick\Desktop\PSC_Coin_Complete\flask_sessions"
app.config["SESSION_PERMANENT"] = True
app.config["SESSION_USE_SIGNER"] = True
app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
app.config["SESSION_COOKIE_SECURE"] = False   # set True after enabling HTTPS
Session(app)
# === END SESSION PERSISTENCE ===

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


# ---------- HMAC signing for client_registry.json ----------
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


# ---------- INTERNAL HELPERS ----------

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


# ---------- STABLE PRODUCT IDs ----------

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


# ---------- ADMIN-SIDE MIRROR ----------

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


# ---------- CLIENT REGISTRY ----------

def _load_clients():
    if not os.path.exists(CLIENTS_FILE):
        return {}
    try:
        with open(CLIENTS_FILE, "rb") as _bf:
            _raw_body = _bf.read()

        if not _verify_clients_signature(_raw_body):
            print(
                "[SECURITY] client_registry.json signature mismatch or "
                "missing. The file has been modified outside the app, or "
                "this is the first run after enabling signing. Treating "
                "load as normal but will re-sign on next save."
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


# ---------- WALLET HELPERS ----------

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


# ============================================================
# ADDITIVE (Option C) â€” TARGET-AWARE PSC CREDITING
# Single credit path used by all verifiers/webhooks.
# target âˆˆ {"spendable","wallet","savings","deposit"}  (default "spendable")
# ============================================================

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
    """
    Credits PSC into the requested pocket.
    - spendable â†’ wallet_psc (existing behaviour)
    - savings   â†’ savings_psc
    - deposit   â†’ deposit_psc (hold-only; not spent by the shop)
    Returns (ok, msg, wallet).
    """
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
    else:  # deposit
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


# ---------- DAILY VISIT BONUS (ADDITIVE) ----------

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
    """
    Calculate the Bonus PSC discount without ever treating Bonus PSC as
    spendable payment currency.

    Bonus PSC is discount-only. Purchased/spendable PSC pays the final
    checkout amount. Savings PSC is only used when the customer explicitly
    selects Savings as the payment source. Deposit PSC is never used here.
    """
    total_client_kes = max(0.0, float(total_client_kes or 0))
    available_bonus_psc = max(0.0, float(available_bonus_psc or 0))

    requested_discount_psc = round(
        total_client_kes * BONUS_DISCOUNT_RATE / PSC_TO_KES_RATE, 4
    )

    # The discount can never exceed the Bonus PSC actually available.
    bonus_used_psc = round(
        min(requested_discount_psc, available_bonus_psc), 4
    )
    discount_psc = bonus_used_psc
    discount_kes = round(discount_psc * PSC_TO_KES_RATE, 2)

    return (
        discount_kes,
        discount_psc,
        bonus_used_psc,
        0.0,  # Bonus PSC never receives payment funding from the wallet.
    )


def deduct_savings_psc(address, amount):
    """Deduct PSC from the Savings pocket only when explicitly selected."""
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
    """
    Make a partial checkout deduction from the explicitly selected
    spendable pocket.

    source='bonus' means Bonus PSC may provide the discount, but payment
    comes ONLY from wallet_psc. source='savings' deducts ONLY savings_psc.
    Bonus PSC is never deducted as order payment.
    """
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
    """Legacy compatibility helper: deduct purchased PSC only.

    Bonus, Savings, and Deposit pockets are never silently consumed by a
    generic balance deduction.
    """
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
    {"key": "phones", "label": "Phones & Tablets", "query": "smartphone", "emoji": "??"},
    {"key": "tv", "label": "TVs & Audio", "query": "smart tv", "emoji": "??"},
    {"key": "appliances", "label": "Appliances", "query": "home appliance", "emoji": "??"},
    {"key": "health", "label": "Health & Beauty", "query": "beauty products", "emoji": "??"},
    {"key": "home", "label": "Home & Office", "query": "home kitchen", "emoji": "??"},
    {"key": "fashion", "label": "Fashion", "query": "fashion", "emoji": "??"},
    {"key": "computing", "label": "Computing", "query": "laptop", "emoji": "??"},
    {"key": "gaming", "label": "Gaming", "query": "gaming console", "emoji": "??"},
    {"key": "groceries", "label": "Groceries", "query": "groceries", "emoji": "??"},
    {"key": "baby", "label": "Baby Products", "query": "baby products", "emoji": "??"},
    {"key": "sports", "label": "Sporting Goods", "query": "sports", "emoji": "?"},
    {"key": "books", "label": "Books", "query": "books", "emoji": "??"},
    {"key": "food", "label": "Food & Pantry", "query": "food", "emoji": "???"},
    {"key": "unga", "label": "Unga & Flour", "query": "unga flour", "emoji": "??"},
    {"key": "sugar", "label": "Sugar & Sweeteners", "query": "sugar", "emoji": "??"},
    {"key": "rice", "label": "Rice & Grains", "query": "rice", "emoji": "??"},
    {"key": "cooking_oil", "label": "Cooking Oil", "query": "cooking oil", "emoji": "??"},
    {"key": "cereals", "label": "Cereals & Breakfast", "query": "cereals", "emoji": "??"},
    {"key": "snacks", "label": "Snacks & Biscuits", "query": "snacks biscuits", "emoji": "??"},
    {"key": "beverages", "label": "Beverages & Drinks", "query": "beverages drinks", "emoji": "??"},
    {"key": "dairy", "label": "Dairy & Eggs", "query": "milk dairy eggs", "emoji": "??"},
    {"key": "meat", "label": "Meat & Fish", "query": "meat fish", "emoji": "??"},
    {"key": "vegetables", "label": "Vegetables & Fruits", "query": "vegetables fruits", "emoji": "??"},
    {"key": "spices", "label": "Spices & Condiments", "query": "spices condiments", "emoji": "??"},
    {"key": "canned", "label": "Canned & Packaged", "query": "canned food", "emoji": "??"},
]



# ---------- PRODUCT SOURCES (file two's sequential scraper) ----------
#
# Replaces the four Playwright-based loaders (load_jumia / load_kilimall /
# load_carrefour / load_jiji) with file two's sequential approach:
#   * Jumia is scraped with requests + BeautifulSoup (fast, no browser)
#   * Kilimall / Carrefour / Jiji use Playwright
#   * Vendors are tried in order and the FIRST successful one wins
#   * Products are returned in file one's format so _register_products()
#     can assign stable IDs and the existing cache layer keeps working
#
# Nothing else in file one (cache, SWR, fallback, /api/*, wallets, VA,
# savings, deposit pocket, payments, templates, CSS) is touched.

_JUMIA_REQUESTS_BLOCKED_UNTIL = 0.0
_JUMIA_REQUESTS_BLOCK_SECONDS = 1800


def _scrape_jumia(q, headers):
    """Jumia scraper. Requests first (fast), Playwright fallback.
    The requests path is disabled for 10 min after any 403 to reduce log noise."""
    global _JUMIA_REQUESTS_BLOCKED_UNTIL
    import requests as _req
    from bs4 import BeautifulSoup as _BS

    url = (f"https://www.jumia.co.ke{q}" if q.startswith("/")
           else f"https://www.jumia.co.ke/catalog/?q={quote_plus(q)}")

    # ---------- FAST PATH: requests (skipped if recently blocked) ----------
    if time.time() >= _JUMIA_REQUESTS_BLOCKED_UNTIL:
        try:
            resp = _req.get(url, headers=headers, timeout=15)
            if resp.status_code == 403:
                _JUMIA_REQUESTS_BLOCKED_UNTIL = time.time() + _JUMIA_REQUESTS_BLOCK_SECONDS
                print(f"[PSC SCRAPE] Jumia 403; requests path disabled for {_JUMIA_REQUESTS_BLOCK_SECONDS}s")
            elif resp.status_code == 200:
                print(f"[PSC SCRAPE] Jumia HTTP 200 for '{q}' ({len(resp.text)} bytes)")
                soup = _BS(resp.text, "html.parser")
                cards = (soup.select("article.prd")
                         or soup.select("article.-pvxs")
                         or soup.select("article[data-catalog-product]")
                         or soup.select("article[data-ga4-item_id]"))
                print(f"[PSC SCRAPE] Jumia matched {len(cards)} cards (requests) for '{q}'")
                products = []
                for i, card in enumerate(cards[:20], start=1):
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

    # ---------- SLOW PATH: Playwright ----------
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                channel="chrome", headless=True,
                args=["--disable-blink-features=AutomationControlled",
                      "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script("Object.defineProperty(navigator, 'webdriver', { get: () => undefined });")
            try: page.goto(url, wait_until="domcontentloaded", timeout=45000)
            except Exception: pass
            page.wait_for_timeout(3000)
            try: page.wait_for_selector("article.prd, article.-pvxs, article[data-catalog-product]", timeout=12000)
            except Exception: pass
            cards = page.query_selector_all("article.prd")
            if not cards: cards = page.query_selector_all("article.-pvxs")
            if not cards: cards = page.query_selector_all("article[data-catalog-product]")
            print(f"[PSC SCRAPE] Jumia matched {len(cards)} cards (Playwright) for '{q}'")
            for i, card in enumerate(cards[:20], start=1):
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
    """Kilimall scraper. Playwright headless Chrome."""
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=True)
            page = browser.new_page(user_agent=headers["User-Agent"])
            page.goto(f"https://www.kilimall.co.ke/search?q={quote_plus(q)}",
                      wait_until="networkidle", timeout=30000)
            try:
                page.wait_for_selector("div.product-item img[src]", timeout=15000)
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
    return []


def _scrape_carrefour(q):
    """Carrefour scraper. Headless Chrome with stealth."""
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                channel="chrome", headless=True,
                args=["--disable-blink-features=AutomationControlled",
                      "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                user_agent=("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                            "AppleWebKit/537.36 (KHTML, like Gecko) "
                            "Chrome/140.0.0.0 Safari/537.36"),
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script("Object.defineProperty(navigator, 'webdriver', { get: () => undefined });")
            try:
                page.goto(
                    f"https://www.carrefour.ke/mafken/en/search?keyword={quote_plus(q)}",
                    wait_until="domcontentloaded", timeout=45000,
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
                    timeout=12000)
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
    """Jiji scraper. Chrome headless."""
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                channel="chrome", headless=True,
                args=["--disable-blink-features=AutomationControlled",
                      "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            try:
                page.goto(f"https://jiji.co.ke/search?query={quote_plus(q)}",
                          wait_until="domcontentloaded", timeout=60000)
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
            for i, card in enumerate(cards[:20], start=1):
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


# ============================================================
# ADDITIVE: 5 EXTRA KENYAN VENDOR SCRAPERS
# 3 generic scrapers + 5 vendor wrappers. Same behavior,
# much shorter than 5 hand-duplicated functions.
# ============================================================


def _scrape_woocommerce(q, url_template, source_label, category, headers):
    """Generic WooCommerce scraper (Fahavi, Copell, etc.)."""
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                channel="chrome", headless=True,
                args=["--disable-blink-features=AutomationControlled",
                      "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script("Object.defineProperty(navigator, 'webdriver', { get: () => undefined });")
            url = url_template.format(q=quote_plus(q))
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=45000)
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
            for i, card in enumerate(cards[:20], start=1):
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
    """Generic Magento scraper (Text Book Centre, Vivo, etc.)."""
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                channel="chrome", headless=True,
                args=["--disable-blink-features=AutomationControlled",
                      "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script("Object.defineProperty(navigator, 'webdriver', { get: () => undefined });")
            url = url_template.format(q=quote_plus(q))
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=45000)
            except Exception:
                pass
            page.wait_for_timeout(3000)
            try:
                page.wait_for_selector(
                    "li.product-item, .product-item-info, ol.products li, "
                    ".product-item, article.product, .product-card",
                    timeout=12000)
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
            for i, card in enumerate(cards[:20], start=1):
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
    """Generic React/Next.js scraper (Naivas and similar)."""
    try:
        from playwright.sync_api import sync_playwright
        products = []
        with sync_playwright() as p:
            browser = p.chromium.launch(
                channel="chrome", headless=True,
                args=["--disable-blink-features=AutomationControlled",
                      "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu"],
            )
            page = browser.new_page(
                user_agent=headers["User-Agent"],
                viewport={"width": 1440, "height": 1000},
                locale="en-KE", timezone_id="Africa/Nairobi",
            )
            page.add_init_script("Object.defineProperty(navigator, 'webdriver', { get: () => undefined });")
            url = url_template.format(q=quote_plus(q))
            try:
                page.goto(url, wait_until="domcontentloaded", timeout=45000)
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
            for i, card in enumerate(cards[:20], start=1):
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


# === END ADDITIVE: 5 EXTRA KENYAN VENDOR SCRAPERS ===

# === ADDITIVE: MASOKO + HOTPOINT + SAMSUNG BRAND STORE ===


def _scrape_masoko(q, headers):
    """Safaricom Masoko � official Safaricom store (React site)."""
    return _scrape_generic_react(
        q, "https://masoko.co.ke/search?q={q}",
        "Safaricom Masoko", "Phones & TVs", headers)


def _scrape_hotpoint(q, headers):
    """Hotpoint Appliances � Hisense-authorised, big TV inventory (Magento)."""
    return _scrape_magento(
        q, "https://hotpoint.co.ke/catalogsearch/result/?q={q}",
        "Hotpoint Appliances", "TVs & Appliances", headers)


def _scrape_samsungstore(q, headers):
    """Samsung Brand Store � official Samsung Kenya store (Magento)."""
    return _scrape_magento(
        q, "https://samsungbrandstore.co.ke/catalogsearch/result/?q={q}",
        "Samsung Brand Store", "Samsung", headers)


# === END ADDITIVE ===


def _scrape_vendors_sequential(query, vendor=None):
    """
    Sequential vendor scraper. Each vendor isolated in its own helper.
    Respects the vendor parameter: if set, ONLY that vendor is attempted.
    """
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
    # === ADDITIVE: 5 EXTRA KENYAN VENDORS ===
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
    # === END ADDITIVE ===

    # === ADDITIVE: MASOKO + HOTPOINT + SAMSUNG BRAND STORE ===
    if vendor in (None, "masoko"):
        p = _scrape_masoko(q, headers)
        if p: return p
    if vendor in (None, "hotpoint"):
        p = _scrape_hotpoint(q, headers)
        if p: return p
    if vendor in (None, "samsungstore"):
        p = _scrape_samsungstore(q, headers)
        if p: return p
    # === END ADDITIVE ===

    try:
        with open('products.json', 'r') as f:
            _fb = json.load(f)
        _fbp = (_fb or {}).get('products', []) or []
        if _fbp:
            print(f"[PSC SCRAPE] All vendors empty for '{q}'; serving products.json ({len(_fbp)}).")
            return _fbp
    except Exception:
        pass
    print(f"[PSC SCRAPE] All vendors empty for '{q}'; hardcoded fallback.")
    return [
        {"id": 1, "name": "Shopping Cart", "price": 10.0, "category": "Essentials", "description": "Durable shopping cart"},
        {"id": 2, "name": "Designer Bag", "price": 25.0, "category": "Fashion", "description": "Eco-friendly designer bag"},
        {"id": 3, "name": "PSC T-Shirt", "price": 15.0, "category": "Apparel", "description": "Comfortable cotton t-shirt"},
        {"id": 4, "name": "PSC Coffee Mug", "price": 8.99, "category": "Kitchen", "description": "Ceramic coffee mug"},
        {"id": 5, "name": "Headphones", "price": 45.0, "category": "Electronics", "description": "Wireless headphones"},
        {"id": 6, "name": "Smart Watch", "price": 89.99, "category": "Electronics", "description": "Feature-rich smart watch"},
    ]


# ---------- END PRODUCT SOURCES ----------


# ============================================================
# PSC SELLER SUBSYSTEM
# Additive. Allows anyone to register as a seller and list items.
# Seller items appear in the shop feed alongside scraped products.
# No existing scraping, wallet, or checkout logic is modified.
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
    """Return ACTIVE seller items matching the query string.

    Matching order (strict):
      1. Exact category_query match  (e.g. "smart tv")
      2. Exact category_key  match   (e.g. "tv")
      3. Exact category label match  (e.g. "TVs & Audio")
      4. Keyword-only match          (every word must appear in keywords)
      5. Fallback: every search word must appear in the full haystack
         (AND logic, not OR)
    """
    q = str(query or "").strip().lower()
    if not q:
        return []
    q_tokens = [w for w in q.split() if len(w) >= 3] or q.split()

    out = []
    for item in _load_seller_items():
        if item.get("status") != "ACTIVE":
            continue

        # --- Exact category matches (fast path, most reliable) ---
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

        # --- Keyword-only match: every query word must be in keywords ---
        kw_blob = " ".join(str(k) for k in (item.get("keywords") or [])).lower()
        if kw_blob and q_tokens and all(w in kw_blob for w in q_tokens):
            out.append(item)
            continue

        # --- Fallback: AND across the full haystack (was previously OR) ---
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
    """Convert a seller item record into a shop product dict."""
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



# ---------------- SELLER IMAGE HANDLING ----------------

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
    """Turn any image source into a locally-hosted URL.
    - empty            -> ""
    - /static/...      -> unchanged
    - http(s)://...    -> download + save, return /static/seller_images/<file>
    - anything else    -> unchanged
    """
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


# ---------------- SELLER PAGES ----------------


@app.route("/sell")
def sell_page():
    return render_template("seller.html")


# ---------------- SELLER API ----------------

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

        # Resolve the seller's chosen category to a CATEGORY_GROUPS
        # entry so we can store its key/query for strict matching later.
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

        # Drop caches so the new item shows up on the very next shop query.
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


# ---------- END SELLER SUBSYSTEM ----------





def _fallback_products(category_label="Sample"):
    products = [
        {
            "name": f"{category_label} - Sample Product A",
            "price": 10.0,
            "kes_price": 1000,
            "client_kes": 1050,
            "category": category_label,
            "image": "",
            "markup": 0.05,
            "source": "Fallback",
            "save_more": False
        },
        {
            "name": f"{category_label} - Sample Product B",
            "price": 25.0,
            "kes_price": 2500,
            "client_kes": 2625,
            "category": category_label,
            "image": "",
            "markup": 0.05,
            "source": "Fallback",
            "save_more": False
        }
    ]
    for product in products:
        product["id"] = _stable_product_id(
            product["name"], product["source"], product["category"], product["kes_price"]
        )
    return products


_INFLIGHT = {}


# ============================================================
#  SWR â€” STALE-WHILE-REVALIDATE BACKGROUND REFRESH
# ============================================================
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
            # Lock busy - give up silently, retry next cycle.
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


def _load_products_live(query, vendor=None):
    """
    Wraps _scrape_vendors_sequential (file two's pipeline).
    Products already carry file two's full dict shape; file one's
    _register_products() only adds stable hashed IDs + vendor_url
    without altering anything else.
    """
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
    # If called from a live Flask request, mark user activity so the
    # background warmer yields the scrape lock.
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
        # === GAP FIX #3 ===
        # Fallback so cooldown windows don't show an empty grid.
                # === FIX 6: never cache fallbacks under the real key; they must be
        # allowed to be replaced the moment real products arrive. ===
        fb = _fallback_products(query.title())
        _register_products(fb)
        return fb

    acquired = _SCRAPE_LOCK.acquire(blocking=True, timeout=60)  # SCRAPE_LOCK_WAIT_FIX
    if not acquired:
        cached = _cache_get_soft(cache_key)
        if cached is not None:
            _register_products(cached)
            return cached
        print(f"[PSC SEARCH] Lock busy for '{vendor or 'all'}:{query}'; serving placeholder.")
        fb = _fallback_products(query.title())
        _register_products(fb)
        return fb
        # === END FIX 6 ===

    try:
        cached = _cache_get(cache_key)
        if cached is not None:
            _register_products(cached)
            return cached

        if _scrape_recently_done(query_key):
            print(f"[PSC SEARCH] '{vendor or 'all'}:{query}' in cooldown after wait, returning empty.")
            # === GAP FIX #3 ===
            fb = _fallback_products(query.title())
            _register_products(fb)
            return fb

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

        # === GAP FIX #3 ===
        # No real products found â€” serve fallback so the shop is never empty.
        print(f"[PSC SEARCH] No real products found for '{vendor or 'all'}:{query}'. Serving fallback.")
        fb = _fallback_products(query.title())
        _register_products(fb)
        # === ADDITIVE: short-lived fallback cache (60s) ===
        _fallback_ttl = 60
        with _CACHE_LOCK:
            _PRODUCT_CACHE_DB[cache_key] = (
                time.time() - (CACHE_TTL_SECONDS - _fallback_ttl), fb
            )
        _cache_save_async()
        return fb
        # === END ADDITIVE ===

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


# ---------- NEW KEYWORDS ----------

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


def _build_hero(products, limit=10):
    with_img = [p for p in products if p.get("image")]
    random.shuffle(with_img)
    return with_img[:limit]


# ---------- MIDNIGHT DAILY BONUS THREAD ----------

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
# BLOCK A + C + D  â€”  FLUTTERWAVE TOP-UP, WITHDRAWALS, PAYOUTS
# ============================================================

FLW_PUBLIC_KEY     = os.getenv("FLW_PUBLIC_KEY", "")
FLW_SECRET_KEY     = os.getenv("FLW_SECRET_KEY", "")
FLW_WEBHOOK_SECRET = os.getenv("FLW_WEBHOOK_SECRET", "")
FLW_BASE_URL       = os.getenv("FLW_BASE_URL", "https://api.flutterwave.com/v3")

PSC_ADMIN_TOKEN       = os.getenv("PSC_ADMIN_TOKEN", "")
PAYOUTS_LIVE          = os.getenv("PAYOUTS_LIVE", "0").strip() == "1"
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


def _flw_headers():
    return {"Authorization": f"Bearer {FLW_SECRET_KEY}", "Content-Type": "application/json"}


def _payments_all():
    d = _jload(PAYMENTS_FILE, [])
    return d if isinstance(d, list) else []


def _payment_find(tx_ref):
    for row in _payments_all():
        if row.get("tx_ref") == tx_ref:
            return row
    return None


def _payment_add(row):
    rows = _payments_all(); rows.append(row); _jsave(PAYMENTS_FILE, rows)


def _payment_update(tx_ref, **fields):
    rows = _payments_all()
    for row in rows:
        if row.get("tx_ref") == tx_ref:
            row.update(fields); _jsave(PAYMENTS_FILE, rows); return row
    return None


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


def _wallet_hold_withdrawal(address, amount_psc, withdrawal_id):
    wallet = get_wallet(address)
    if not wallet:
        return False, "Wallet not found", None
    amt = round(float(amount_psc), 2)
    available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
    if available - amt < 1.00 - 1e-9:
        return False, (f"Insufficient spendable balance. Available "
                       f"{available:.2f} PSC. At least 1.00 PSC must remain "
                       f"in the account."), wallet
    wallet["wallet_psc"] = round(available - amt, 2)
    wallet.setdefault("held_psc", 0.0)
    wallet["held_psc"] = round(float(wallet.get("held_psc", 0) or 0) + amt, 2)
    wallet.setdefault("withdrawals", [])
    wallet["withdrawals"].append({
        "withdrawal_id": withdrawal_id, "amount_psc": amt,
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
    if outcome == "REJECTED":
        wallet["wallet_psc"] = round(float(wallet.get("wallet_psc", 0) or 0) + amt, 2)
    for w in wallet.get("withdrawals", []):
        if w.get("withdrawal_id") == withdrawal_id:
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


@app.route("/api/psc/topup/initiate", methods=["POST"])
def api_psc_topup_initiate():
    try:
        _peek = request.get_json(silent=True) or {}
    except Exception:
        _peek = {}
    _requested_gw = str(_peek.get("gateway") or _peek.get("provider") or "").strip().lower()
    if _requested_gw == "paystack":
        return api_psc_topup_initiate_ps()

    if not FLW_SECRET_KEY:
        return jsonify({"success": False,
                        "message": "Flutterwave keys not configured in .env"}), 500
    try:
        data = request.get_json() or {}

        user = session.get("user")
        session_wallet = session.get("wallet", "")
        if not user or not session_wallet:
            return jsonify({
                "success": False,
                "message": "Please log in to your account before buying PSC."
            }), 401

        address = str(data.get("wallet") or session_wallet or "").strip()
        if not address:
            return jsonify({"success": False, "message": "wallet is required"}), 400
        if address != session_wallet:
            return jsonify({
                "success": False,
                "message": "Wallet does not match the logged-in account."
            }), 403

        verified_phone = session.get("verified_phone", "")
        if not verified_phone:
            return jsonify({
                "success": False,
                "message": "Please verify your phone at checkout before buying PSC."
            }), 403

        client = get_client_by_phone(verified_phone)
        if not client:
            return jsonify({
                "success": False,
                "message": "No registered account found for your phone number."
            }), 404

        client_wallet = str(client.get("wallet_address", "")).strip()
        if client_wallet != address:
            return jsonify({
                "success": False,
                "message": "Your verified phone does not belong to this wallet."
            }), 403

        amount_kes = float(data.get("amount_kes") or 0)
        redirect_url = str(data.get("redirect_url") or "").strip()

        if amount_kes < 1:
            return jsonify({"success": False,
                            "message": "amount_kes must be at least 1"}), 400

        wallet = get_wallet(address)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"}), 404

        # ADDITIVE (Option C): capture credit target on the payment record.
        _target = _normalize_credit_target(
            data.get("target") or data.get("credit_target") or "spendable"
        )

        tx_ref = "PSC-" + uuid.uuid4().hex[:16]
        expected_psc = round(amount_kes / PSC_TO_KES_RATE, 2)

        _payment_add({
            "tx_ref": tx_ref, "wallet_address": address,
            "amount_kes": round(amount_kes, 2), "expected_psc": expected_psc,
            "status": "PENDING", "provider": "flutterwave",
            "flw_tx_id": None, "created_at": _now(),
            "verified_at": None, "credited_psc": 0.0,
            "target": _target,
        })

        payload = {
            "tx_ref": tx_ref,
            "amount": str(round(amount_kes, 2)),
            "currency": "KES",
            "redirect_url": redirect_url or request.url_root.rstrip("/") + "/psc_topup_return",
            "payment_options": "card,mpesa,banktransfer,ussd",
            "customer": {
                "email": client.get("email") or "customer@example.com",
                "phonenumber": client.get("phone") or verified_phone or "",
                "name": client.get("name") or (user.get("name") if user else "") or "PSC Customer",
            },
            "customizations": {
                "title": "PSC Top-Up",
                "description": f"Buy {expected_psc} PSC for KES {amount_kes:.2f}",
            },
        }
        r = _http.post(f"{FLW_BASE_URL}/payments", json=payload,
                       headers=_flw_headers(), timeout=20)
        resp = r.json() if r.content else {}

        print(f"[FLW] status={r.status_code} resp={str(resp)[:400]}")

        if r.status_code >= 300 or resp.get("status") != "success":
            _payment_update(tx_ref, status="FAILED",
                            error=str(resp.get("message") or r.text)[:300])
            return jsonify({"success": False,
                            "message": resp.get("message") or "Flutterwave error"}), 502

        return jsonify({
            "success": True, "tx_ref": tx_ref,
            "checkout_url": resp["data"]["link"],
            "amount_kes": round(amount_kes, 2),
            "expected_psc": expected_psc,
            "gateway": "flutterwave",
            "target": _target,
            "message": "Open the checkout link to complete payment.",
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


def _verify_and_credit(tx_ref, flw_tx_id):
    row = _payment_find(tx_ref)
    if not row:
        return False, "Unknown tx_ref", None
    if row.get("status") == "COMPLETED":
        return True, "Already credited", row
    if row.get("status") == "FAILED":
        return False, "Payment previously marked FAILED", row
    if not FLW_SECRET_KEY:
        return False, "Flutterwave keys not configured", row
    try:
        r = _http.get(f"{FLW_BASE_URL}/transactions/{flw_tx_id}/verify",
                      headers=_flw_headers(), timeout=20)
        resp = r.json() if r.content else {}
        if r.status_code >= 300 or resp.get("status") != "success":
            return False, resp.get("message") or "Verify call failed", row

        d = resp.get("data") or {}
        got_amount   = float(d.get("amount") or 0)
        got_currency = str(d.get("currency") or "").upper()
        got_status   = str(d.get("status") or "").lower()
        got_ref      = str(d.get("tx_ref") or "")

        if got_ref != tx_ref:
            return False, "tx_ref mismatch", row
        if got_status != "successful":
            _payment_update(tx_ref, status="FAILED", flw_tx_id=flw_tx_id,
                            error=f"provider status={got_status}")
            return False, f"Provider status: {got_status}", row
        if got_currency != "KES":
            _payment_update(tx_ref, status="FAILED", flw_tx_id=flw_tx_id,
                            error=f"currency={got_currency}")
            return False, "Currency mismatch", row
        if got_amount + 0.01 < float(row.get("amount_kes") or 0):
            _payment_update(tx_ref, status="FAILED", flw_tx_id=flw_tx_id,
                            error=f"amount {got_amount} < expected {row.get('amount_kes')}")
            return False, "Amount less than expected", row

        psc_amount = float(row["expected_psc"])
        kes_amount = float(row["amount_kes"])

        # ADDITIVE (Option C): route to the requested pocket.
        _target = _normalize_credit_target(row.get("target") or "spendable")
        ok, msg, _wallet = _add_psc_to_target(
            row["wallet_address"], psc_amount,
            target=_target, kes_amount=kes_amount,
            payment_reference=tx_ref,
            audit_type="FLW_TOPUP",
        )
        if not ok:
            _payment_update(tx_ref, status="FAILED", flw_tx_id=flw_tx_id,
                            error=f"credit failed: {msg}")
            return False, f"Credit failed: {msg}", row

        _payment_update(tx_ref, status="COMPLETED", flw_tx_id=flw_tx_id,
                        verified_at=_now(), credited_psc=psc_amount, error="")

        _close_partial_if_any(row["wallet_address"])
        return True, f"Credited {psc_amount:.2f} PSC", _payment_find(tx_ref)
    except Exception as e:
        return False, str(e), row


@app.route("/api/psc/topup/verify", methods=["POST"])
def api_psc_topup_verify():
    try:
        _peek = request.get_json(silent=True) or {}
    except Exception:
        _peek = {}
    _requested_gw = str(_peek.get("gateway") or _peek.get("provider") or "").strip().lower()
    if _requested_gw == "paystack":
        return api_psc_topup_verify_ps()

    try:
        data = request.get_json() or {}
        tx_ref = str(data.get("tx_ref") or "").strip()
        flw_tx_id = data.get("transaction_id") or data.get("flw_tx_id")
        if not tx_ref or not flw_tx_id:
            return jsonify({"success": False, "message": "tx_ref and transaction_id required"}), 400
        ok, msg, row = _verify_and_credit(tx_ref, flw_tx_id)
        return jsonify({"success": ok, "message": msg, "payment": row,
                        "gateway": "flutterwave"}), (200 if ok else 400)
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/webhooks/flutterwave", methods=["POST"])
def webhook_flutterwave():
    try:
        if not FLW_WEBHOOK_SECRET:
            return jsonify({"success": False,
                            "message": "webhook secret not configured"}), 401
        sent = request.headers.get("verif-hash", "")
        if not hmac.compare_digest(sent, FLW_WEBHOOK_SECRET):
            return jsonify({"success": False, "message": "bad signature"}), 401

        body = request.get_json(silent=True) or {}
        d = body.get("data") or {}
        tx_ref = str(d.get("tx_ref") or "").strip()
        flw_tx_id = d.get("id")
        if not tx_ref or not flw_tx_id:
            return jsonify({"success": True, "message": "ignored"}), 200
        _verify_and_credit(tx_ref, flw_tx_id)
        return jsonify({"success": True}), 200
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/psc/topup/status/<tx_ref>")
def api_psc_topup_status(tx_ref):
    row = _payment_find(tx_ref)
    if not row:
        return jsonify({"success": False, "message": "not found"}), 404
    return jsonify({"success": True, "payment": row, "gateway": "flutterwave"})


@app.route("/api/psc/topup/history/<address>")
def api_psc_topup_history(address):
    rows = [r for r in _payments_all() if r.get("wallet_address") == address]
    return jsonify({"success": True, "payments": rows, "gateway": "flutterwave"})


@app.route("/psc_topup_return")
def psc_topup_return_page():
    return render_template("psc_topup_return.html")


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
            row = None
            for p in reversed(_payments_all()):
                if p.get("wallet_address") == address and p.get("status") == "COMPLETED":
                    row = p; break
            if not row:
                return jsonify({"success": False,
                                "message": "No completed card payment found to refund."}), 400
            dest = f"card-of:{row['tx_ref']}"
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
                        f"Waiting for admin to review and pay."),
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


def _flw_transfer(row):
    method = row.get("method")
    dest = str(row.get("destination") or "")
    amount_kes = float(row.get("amount_kes") or 0)

    if method == "mpesa":
        num = dest.replace("+", "").strip()
        if num.startswith("0"): num = "254" + num[1:]
        elif not num.startswith("254"): num = "254" + num
        payload = {
            "account_bank": "MPS",
            "account_number": num,
            "amount": amount_kes,
            "narration": f"PSC payout {row['withdrawal_id']}",
            "currency": "KES",
            "reference": row["withdrawal_id"],
            "callback_url": request.url_root.rstrip("/") + "/webhooks/flutterwave",
            "debit_currency": "KES",
        }
    elif method == "bank":
        payload = {
            "account_bank": str(row.get("bank_code") or "").strip(),
            "account_number": dest,
            "amount": amount_kes,
            "narration": f"PSC payout {row['withdrawal_id']}",
            "currency": "KES",
            "reference": row["withdrawal_id"],
            "callback_url": request.url_root.rstrip("/") + "/webhooks/flutterwave",
            "debit_currency": "KES",
        }
    elif method == "card-refund":
        tx_ref = dest.split("card-of:", 1)[1] if "card-of:" in dest else ""
        pay = _payment_find(tx_ref)
        if not pay or not pay.get("flw_tx_id"):
            return False, {}, "Original card transaction not found"
        r = _http.post(
            f"{FLW_BASE_URL}/transactions/{pay['flw_tx_id']}/refund",
            json={"amount": amount_kes},
            headers=_flw_headers(), timeout=20,
        )
        resp = r.json() if r.content else {}
        ok = r.status_code < 300 and resp.get("status") == "success"
        return ok, resp, ("" if ok else str(resp.get("message") or r.text)[:300])
    else:
        return False, {}, "Unsupported method"

    r = _http.post(f"{FLW_BASE_URL}/transfers", json=payload, headers=_flw_headers(), timeout=20)
    resp = r.json() if r.content else {}
    ok = r.status_code < 300 and resp.get("status") == "success"
    return ok, resp, ("" if ok else str(resp.get("message") or r.text)[:300])


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

        if not PAYOUTS_LIVE:
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
                            "message": "Recorded as manually paid (PAYOUTS_LIVE=0)."})

        ok, info, err = _flw_transfer(row)
        if not ok:
            _audit_add({"withdrawal_id": wid, "amount_kes": amount_kes, "method": row.get("method"),
                        "at": _now(), "mode": "auto", "result": "FAIL", "error": err,
                        "flw_response": info})
            return jsonify({"success": False, "message": err or "Flutterwave transfer failed",
                            "withdrawal": _wq_find(wid)}), 502

        transfer_id = (info.get("data") or {}).get("id") if isinstance(info, dict) else None
        _wq_update(wid, status="PAID", settled_at=_now(),
                   transfer_id=transfer_id, mode="auto", flw_response=info)
        _wallet_release_or_settle(row["wallet_address"], float(row["amount_psc"]), wid, "PAID")
        _ledger_update(wid, status="PAID", settled_at=_now(),
                       transfer_id=transfer_id, mode="auto")
        _audit_add({"withdrawal_id": wid, "amount_kes": amount_kes, "method": row.get("method"),
                    "at": _now(), "mode": "auto", "result": "SUCCESS",
                    "transfer_id": transfer_id})
        _record_payout_velocity(row["wallet_address"], amount_kes, "AUTO_PAID")
        _maybe_cbk_report(row, amount_kes)
        return jsonify({"success": True, "withdrawal": _wq_find(wid),
                        "transfer_id": transfer_id,
                        "message": "Flutterwave transfer sent."})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# END BLOCK A + C + D
# ============================================================


# ============================================================
# PAYSTACK GATEWAY â€” ADDITIVE, OFF BY DEFAULT
# ============================================================

PAYSTACK_ENABLED        = os.getenv("PAYSTACK_ENABLED", "0").strip() == "1"
PAYSTACK_SECRET_KEY     = os.getenv("PAYSTACK_SECRET_KEY", "")
PAYSTACK_PUBLIC_KEY     = os.getenv("PAYSTACK_PUBLIC_KEY", "")
PAYSTACK_WEBHOOK_SECRET = os.getenv("PAYSTACK_WEBHOOK_SECRET", "")
PAYSTACK_BASE_URL       = os.getenv("PAYSTACK_BASE_URL", "https://api.paystack.co")
PAYSTACK_CURRENCY       = os.getenv("PAYSTACK_CURRENCY", "KES").strip().upper()

PAYSTACK_PAYMENTS_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "paystack_payments.json"
)


def _ps_headers():
    return {
        "Authorization": f"Bearer {PAYSTACK_SECRET_KEY}",
        "Content-Type": "application/json",
    }


def _ps_payments_all():
    d = _jload(PAYSTACK_PAYMENTS_FILE, [])
    return d if isinstance(d, list) else []


def _ps_payment_find(tx_ref):
    for row in _ps_payments_all():
        if row.get("tx_ref") == tx_ref:
            return row
    return None


def _ps_payment_add(row):
    rows = _ps_payments_all()
    rows.append(row)
    _jsave(PAYSTACK_PAYMENTS_FILE, rows)


def _ps_payment_update(tx_ref, **fields):
    rows = _ps_payments_all()
    for r in rows:
        if r.get("tx_ref") == tx_ref:
            r.update(fields)
            _jsave(PAYSTACK_PAYMENTS_FILE, rows)
            return r
    return None


@app.route("/api/payments/gateways", methods=["GET"])
def api_payments_gateways():
    gateways = []
    if FLW_SECRET_KEY:
        gateways.append({
            "key": "flutterwave", "label": "Flutterwave",
            "default": True, "currencies": ["KES"],
        })
    if PAYSTACK_ENABLED and PAYSTACK_SECRET_KEY:
        gateways.append({
            "key": "paystack", "label": "Paystack",
            "default": len(gateways) == 0, "currencies": [PAYSTACK_CURRENCY],
        })
    if COINGATE_ENABLED and COINGATE_API_TOKEN:
        gateways.append({
            "key": "coingate",
            "label": "CoinGate (Crypto)",
            "default": False,
            "currencies": COINGATE_ALLOWED_CURRENCIES,
            "settle_currency": COINGATE_SETTLE_CUR,
            "min_kes": COINGATE_MIN_KES,
            "max_kes": COINGATE_MAX_KES,
        })

    if MOONPAY_ENABLED and MOONPAY_PUBLISHABLE_KEY:
        gateways.append({
            "key": "moonpay",
            "label": "MoonPay (Crypto)",
            "default": False,
            "currencies": [c.upper() for c in MOONPAY_ALLOWED_CRYPTOS],
            "fiat_currency": MOONPAY_CURRENCY_CODE.upper(),
            "min_kes": MOONPAY_MIN_KES,
            "max_kes": MOONPAY_MAX_KES,
            "mode": MOONPAY_MODE,
        })
    return jsonify({"success": True, "gateways": gateways})


@app.route("/api/psc/topup/initiate_ps", methods=["POST"])
def api_psc_topup_initiate_ps():
    if not PAYSTACK_ENABLED:
        return jsonify({"success": False,
                        "message": "Paystack is disabled (PAYSTACK_ENABLED=0)."}), 503
    if not PAYSTACK_SECRET_KEY:
        return jsonify({"success": False,
                        "message": "Paystack keys not configured in .env"}), 500
    try:
        data = request.get_json() or {}

        user = session.get("user")
        session_wallet = session.get("wallet", "")
        if not user or not session_wallet:
            return jsonify({
                "success": False,
                "message": "Please log in to your account before buying PSC."
            }), 401

        address = str(data.get("wallet") or session_wallet or "").strip()
        if not address:
            return jsonify({"success": False, "message": "wallet is required"}), 400
        if address != session_wallet:
            return jsonify({
                "success": False,
                "message": "Wallet does not match the logged-in account."
            }), 403

        verified_phone = session.get("verified_phone", "")
        if not verified_phone:
            return jsonify({
                "success": False,
                "message": "Please verify your phone at checkout before buying PSC."
            }), 403

        client = get_client_by_phone(verified_phone)
        if not client:
            return jsonify({
                "success": False,
                "message": "No registered account found for your phone number."
            }), 404

        client_wallet = str(client.get("wallet_address", "")).strip()
        if client_wallet != address:
            return jsonify({
                "success": False,
                "message": "Your verified phone does not belong to this wallet."
            }), 403

        amount_kes = float(data.get("amount_kes") or 0)
        redirect_url = str(data.get("redirect_url") or "").strip()

        if amount_kes < 1:
            return jsonify({"success": False,
                            "message": "amount_kes must be at least 1"}), 400

        wallet = get_wallet(address)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"}), 404

        amount_subunit = int(round(amount_kes * 100))

        # ADDITIVE (Option C): capture credit target on the payment record.
        _target = _normalize_credit_target(
            data.get("target") or data.get("credit_target") or "spendable"
        )

        tx_ref = "PSC-PS-" + uuid.uuid4().hex[:16]
        expected_psc = round(amount_kes / PSC_TO_KES_RATE, 2)

        _ps_payment_add({
            "tx_ref": tx_ref,
            "wallet_address": address,
            "amount_kes": round(amount_kes, 2),
            "expected_psc": expected_psc,
            "status": "PENDING",
            "provider": "paystack",
            "ps_reference": None,
            "created_at": _now(),
            "verified_at": None,
            "credited_psc": 0.0,
            "target": _target,
        })

        payload = {
            "email": client.get("email") or "customer@example.com",
            "amount": amount_subunit,
            "currency": PAYSTACK_CURRENCY,
            "reference": tx_ref,
            "callback_url": redirect_url or (
                request.url_root.rstrip("/") + "/psc_topup_return"
            ),
            "metadata": {
                "wallet": address,
                "phone": client.get("phone") or verified_phone or "",
                "name": client.get("name") or (user.get("name") if user else "") or "PSC Customer",
                "expected_psc": expected_psc,
                "target": _target,
                "custom_fields": [
                    {"display_name": "Wallet", "variable_name": "wallet", "value": address},
                    {"display_name": "PSC", "variable_name": "expected_psc", "value": f"{expected_psc}"},
                    {"display_name": "Target", "variable_name": "target", "value": _target},
                ],
            },
        }
        r = _http.post(f"{PAYSTACK_BASE_URL}/transaction/initialize",
                       json=payload, headers=_ps_headers(), timeout=20)
        resp = r.json() if r.content else {}

        print(f"[PAYSTACK] status={r.status_code} resp={str(resp)[:400]}")

        if r.status_code >= 300 or not resp.get("status"):
            _ps_payment_update(tx_ref, status="FAILED",
                               error=str(resp.get("message") or r.text)[:300])
            return jsonify({"success": False,
                            "message": resp.get("message") or "Paystack error"}), 502

        pdata = resp.get("data") or {}
        return jsonify({
            "success": True,
            "tx_ref": tx_ref,
            "checkout_url": pdata.get("authorization_url"),
            "access_code": pdata.get("access_code"),
            "reference": pdata.get("reference") or tx_ref,
            "amount_kes": round(amount_kes, 2),
            "expected_psc": expected_psc,
            "gateway": "paystack",
            "target": _target,
            "message": "Open the checkout link to complete payment.",
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


def _ps_verify_and_credit(tx_ref, ps_reference=None):
    row = _ps_payment_find(tx_ref)
    if not row:
        return False, "Unknown tx_ref", None
    if row.get("status") == "COMPLETED":
        return True, "Already credited", row
    if row.get("status") == "FAILED":
        return False, "Payment previously marked FAILED", row
    if not PAYSTACK_SECRET_KEY:
        return False, "Paystack keys not configured", row

    try:
        ref = str(ps_reference or row.get("ps_reference") or tx_ref).strip()
        r = _http.get(f"{PAYSTACK_BASE_URL}/transaction/verify/{quote_plus(ref)}",
                      headers=_ps_headers(), timeout=20)
        resp = r.json() if r.content else {}
        if r.status_code >= 300 or not resp.get("status"):
            return False, resp.get("message") or "Verify call failed", row

        d = resp.get("data") or {}
        got_status   = str(d.get("status") or "").lower()
        got_currency = str(d.get("currency") or "").upper()
        got_amount_sub = int(d.get("amount") or 0)
        got_amount_kes = round(got_amount_sub / 100.0, 2)
        got_reference  = str(d.get("reference") or "").strip()

        if got_reference and got_reference != tx_ref and got_reference != ref:
            return False, "reference mismatch", row

        if got_status != "success":
            _ps_payment_update(tx_ref, status="FAILED", ps_reference=got_reference,
                               error=f"provider status={got_status}")
            return False, f"Provider status: {got_status}", row

        if got_currency != PAYSTACK_CURRENCY:
            _ps_payment_update(tx_ref, status="FAILED", ps_reference=got_reference,
                               error=f"currency={got_currency}")
            return False, "Currency mismatch", row

        if got_amount_kes + 0.01 < float(row.get("amount_kes") or 0):
            _ps_payment_update(tx_ref, status="FAILED", ps_reference=got_reference,
                               error=f"amount {got_amount_kes} < expected {row.get('amount_kes')}")
            return False, "Amount less than expected", row

        psc_amount = float(row["expected_psc"])
        kes_amount = float(row["amount_kes"])

        # ADDITIVE (Option C): route to the requested pocket.
        _target = _normalize_credit_target(row.get("target") or "spendable")
        ok, msg, _wallet = _add_psc_to_target(
            row["wallet_address"], psc_amount,
            target=_target, kes_amount=kes_amount,
            payment_reference=f"PS:{tx_ref}",
            audit_type="PAYSTACK_TOPUP",
        )
        if not ok:
            _ps_payment_update(tx_ref, status="FAILED", ps_reference=got_reference,
                               error=f"credit failed: {msg}")
            return False, f"Credit failed: {msg}", row

        _ps_payment_update(tx_ref, status="COMPLETED", ps_reference=got_reference,
                           verified_at=_now(), credited_psc=psc_amount, error="")
        _close_partial_if_any(row["wallet_address"])
        return True, f"Credited {psc_amount:.2f} PSC", _ps_payment_find(tx_ref)
    except Exception as e:
        return False, str(e), row


@app.route("/api/psc/topup/verify_ps", methods=["POST"])
def api_psc_topup_verify_ps():
    try:
        data = request.get_json() or {}
        tx_ref = str(data.get("tx_ref") or "").strip()
        ps_reference = data.get("reference") or data.get("ps_reference") or tx_ref
        if not tx_ref:
            return jsonify({"success": False, "message": "tx_ref required"}), 400
        ok, msg, row = _ps_verify_and_credit(tx_ref, ps_reference)
        return jsonify({"success": ok, "message": msg, "payment": row,
                        "gateway": "paystack"}), (200 if ok else 400)
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/psc/topup/status_ps/<tx_ref>")
def api_psc_topup_status_ps(tx_ref):
    row = _ps_payment_find(tx_ref)
    if not row:
        return jsonify({"success": False, "message": "not found"}), 404
    return jsonify({"success": True, "payment": row, "gateway": "paystack"})


@app.route("/api/psc/topup/history_ps/<address>")
def api_psc_topup_history_ps(address):
    rows = [r for r in _ps_payments_all() if r.get("wallet_address") == address]
    return jsonify({"success": True, "payments": rows, "gateway": "paystack"})


@app.route("/webhooks/paystack", methods=["POST"])
def webhook_paystack():
    try:
        if not PAYSTACK_SECRET_KEY:
            return jsonify({"success": False,
                            "message": "paystack secret not configured"}), 401

        raw_body = request.get_data() or b""
        sent_sig = request.headers.get("x-paystack-signature", "")

        expected_sig = hmac.new(
            PAYSTACK_SECRET_KEY.encode("utf-8"),
            raw_body,
            hashlib.sha512,
        ).hexdigest()

        if not sent_sig or not hmac.compare_digest(sent_sig, expected_sig):
            return jsonify({"success": False, "message": "bad signature"}), 401

        body = json.loads(raw_body.decode("utf-8") or "{}")
        event = str(body.get("event") or "").strip().lower()
        d = body.get("data") or {}

        if event == "charge.success":
            tx_ref = str(d.get("reference") or "").strip()
            if not tx_ref:
                return jsonify({"success": True, "message": "ignored"}), 200
            _ps_verify_and_credit(tx_ref, ps_reference=tx_ref)
            return jsonify({"success": True}), 200

        if event in ("refund.processed", "charge.reversed"):
            tx_ref = str(d.get("reference") or "").strip()
            row = _ps_payment_find(tx_ref)
            if row and row.get("status") == "COMPLETED":
                row["status"] = "REVERSED"
                row["reversed_at"] = _now()
                _jsave(PAYSTACK_PAYMENTS_FILE, _ps_payments_all())
                wallet_addr = row.get("wallet_address")
                psc = float(row.get("credited_psc") or 0)
                if wallet_addr and psc > 0:
                    try:
                        deduct_wallet_psc(wallet_addr, psc)
                    except Exception:
                        pass
                _admin_ledger_add({
                    "type": "PS_REVERSAL",
                    "wallet_address": wallet_addr,
                    "tx_ref": tx_ref,
                    "amount_psc": psc,
                    "status": "REVERSED",
                    "time": _now(),
                })
            return jsonify({"success": True}), 200

        return jsonify({"success": True, "message": "ignored"}), 200
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# END PAYSTACK GATEWAY
# ============================================================


# ---------- CATEGORY IMAGES ENDPOINT (CACHE-FIRST, BACKGROUND SCRAPE) ----------
@app.route("/api/category_images")
def api_category_images():
    """
    Fast, cache-first endpoint. Never scrapes inline.

    Fast path (99% of requests):
      - Read _CATEGORY_IMAGE_CACHE or _PRODUCT_CACHE_DB.
      - Return whatever is cached; falls back to emoji placeholders.
      - Response time: a few milliseconds.

    Slow path (cache is cold for a category):
      - Schedule a background refresh via _background_refresh_products().
      - Return the emoji placeholder immediately.
      - On the next call (page auto-refreshes every 2 min), real images
        will already be in the cache.

    The actual scraping still happens â€” Jumia / Kilimall / Carrefour â€”
    but on daemon threads, never blocking the user request.
    """
    try:
        result = {}

        for cat in CATEGORY_GROUPS:
            key = cat["key"]

            # -------- FAST PATH 1: category-image memo --------
            cached = _CATEGORY_IMAGE_CACHE.get(key)
            if cached and (time.time() - cached.get("ts", 0)) < _CATEGORY_IMAGE_TTL:
                result[key] = {
                    "image": cached.get("image", ""),
                    "name":  cached.get("name", ""),
                    "emoji": cat.get("emoji", ""),
                }
                continue

            # -------- FAST PATH 2: product cache --------
            products = _cache_get(f"products::all::{cat['query'].lower()}") or []
            if not products:
                products = _cache_get(f"products::{cat['query'].lower()}") or []
            if not products:
                products = _cache_get_soft(f"products::all::{cat['query'].lower()}") or []

            pick = None
            for p in products:
                if p and p.get("image"):
                    pick = p
                    break

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

            # -------- SLOW PATH: cold cache â†’ schedule bg refresh --------
            # Uses the same SWR function the rest of the app already uses.
            # Spawns a daemon thread; does NOT block this request.
            # Respects the existing _SCRAPE_LOCK, so it cannot collide
            # with the warmer or with /api/products.
            try:
                _background_refresh_products(
                    cat["query"],
                    vendor=None,
                    cache_key=f"products::all::{cat['query'].lower()}",
                )
            except Exception as e:
                print(f"[CAT-IMG] background refresh schedule failed for {key}: {e}")

            # Return the placeholder immediately â€” do NOT wait.
            result[key] = {
                "image": "",
                "name":  "",
                "emoji": cat.get("emoji", ""),
            }

        return jsonify({"success": True, "images": result,
                        "psc_to_kes_rate": PSC_TO_KES_RATE,
                        "cached_only": True})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ---------- VENDOR INFO ENDPOINT (CLIENT-SAFE STUB) ----------
@app.route("/api/vendors")
def api_vendors():
    return jsonify({
        "success": True,
        "psc_to_kes_rate": PSC_TO_KES_RATE,
        "vendors": [],
    })


# ---------- CLIENT SEARCH (HIDES VENDORS) ----------
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

               # NEW: extract vendor hint before sanitizing
        vendor_hint, _ = _extract_vendor_hint(raw_q)
        q = _normalize_search_query(raw_q)

        if not q:
            return jsonify({
                "success": False,
                "message": "Type something to search.",
                "products": [],
            }), 400

        products = load_products(q, vendor=vendor_hint)

        products = load_products(q, vendor=None)
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


# ---------- ROUTES ----------

@app.route("/")
def index():
    raw_query = request.args.get("q", "").strip()
    category_key = request.args.get("category", "").strip()

       # NEW: extract vendor hint from the raw query
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
                categories=CATEGORY_GROUPS,
                new_items=[],
                top_selling=[],
                hero_items=_strip_products_for_client(hero),
                wallet=wallet,
                balance=balance,
                user=user,
            )

    if query:
        products = load_products(query, vendor=vendor)

        # If the exact query returned nothing, retry with just the first
        # word. Example: "iphone 18" -> "iphone". Prevents fallback for
        # specific model-year searches that no vendor stocks.
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
        categories=CATEGORY_GROUPS,
        new_items=_strip_products_for_client(new_items),
        top_selling=_strip_products_for_client(top_selling),
        hero_items=_strip_products_for_client(hero_items),
        wallet=wallet,
        balance=balance,
        user=user,
    )


# ---------- ACCOUNT (REGISTER / LOGIN) ----------

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


# ---------- WALLET ----------

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
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({
            "success": False,
            "message": ("This endpoint is for the admin wallet system only. "
                        "Use 'Buy PSC' on the shop page to top up through "
                        "Flutterwave, or have the admin credit your account.")
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

        # ADDITIVE (Option C): allow admin to specify target too.
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
            "message": f"Purchased {psc_amount:.2f} PSC for KES {kes_amount:.2f}.",
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
                        f"You will be credited {psc_amount:.2f} PSC."),
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


# ---------- CHECKOUT PAYMENT LOGIC ----------

def calculate_checkout_payment(wallet, gross_psc, total_client_kes, payment_source="auto"):
    """
    Controlled checkout accounting:
      * Bonus PSC = discount only.
      * wallet_psc = purchased/spendable payment balance.
      * savings_psc = payment balance only when Savings is explicitly selected.
      * deposit_psc = never used for shopping.
      * auto/bonus uses wallet_psc for payment and applies the Bonus discount.
    """
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

    # Minimum shopping balance applies to the actual payment pocket, not the
    # Bonus pocket. Bonus PSC is a discount instrument, never payment money.
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
    """Apply only the payment pocket selected by calculate_checkout_payment."""
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
    """Restore a checkout deduction if order persistence fails."""
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


# ---------- CHECKOUT PREVIEW ----------

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


# ---------- ORDERS ----------

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


# ---------- LIVE PRODUCTS FEED (CLIENT-SAFE) ----------

@app.route("/api/products")
def api_products():
    try:
        raw_q = request.args.get("q", "electronics")
        cat_key = request.args.get("category", "").strip()
        light = request.args.get("light", "") == "1"

        # ADDITIVE: extract vendor hint so masoko:phone etc force the vendor
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


# ---------- CACHE ADMIN ----------

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


# ---------- ADDITIVE: EXPLICIT BACKGROUND REFRESH ----------

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


# ---------- CART CHECKOUT ----------

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
# VIRTUAL ACCOUNT (VA) + COMPLIANCE LAYER â€” FULLY ADDITIVE
# ============================================================

VA_ENABLED               = os.getenv("VA_ENABLED", "0").strip() == "1"
VA_COUNTRY               = os.getenv("VA_COUNTRY", "KE").strip().upper()
VA_CURRENCY              = os.getenv("VA_CURRENCY", "KES").strip().upper()
VA_MIN_KES               = float(os.getenv("VA_MIN_KES", "10") or 10)
VA_MAX_KES               = float(os.getenv("VA_MAX_KES", "150000") or 150000)
VA_DAILY_MAX_KES         = float(os.getenv("VA_DAILY_MAX_KES", "300000") or 300000)
VA_LIFETIME_MAX_KES      = float(os.getenv("VA_LIFETIME_MAX_KES", "2000000") or 2000000)
VA_MAX_PER_DAY           = int(os.getenv("VA_MAX_PER_DAY", "20") or 20)
VA_EXPIRY_DAYS           = int(os.getenv("VA_EXPIRY_DAYS", "3650") or 3650)

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
VA_FILE              = os.path.join(VA_DIR, "virtual_accounts.json")
VA_CREDITS_FILE      = os.path.join(VA_DIR, "va_credits.json")
VA_AUDIT_FILE        = os.path.join(VA_DIR, "va_audit.json")
KYC_FILE             = os.path.join(VA_DIR, "kyc_records.json")
COMPLIANCE_FILE      = os.path.join(VA_DIR, "compliance_flags.json")
VELOCITY_FILE        = os.path.join(VA_DIR, "payout_velocity.json")
CBK_REPORT_FILE      = os.path.join(VA_DIR, "cbk_reports.json")
BANK_CACHE_FILE      = os.path.join(VA_DIR, "bank_list_cache.json")
SANCTIONS_FILE       = os.path.join(VA_DIR, "sanctions_blocklist.txt")

_SANCTIONS_INLINE = set(
    x.strip().lower() for x in
    os.getenv("SANCTIONS_BLOCKLIST", "").split(",") if x.strip()
)

_VA_LOCK = threading.Lock()
_BANK_CACHE_LOCK = threading.Lock()
_BANK_CACHE_TTL = 86400


def _va_load(path, default):
    return _jload(path, default)


# === FIX #A ===
# Original code had two definitions of _va_save: one taking (path, data)
# and one taking (d). The second silently shadowed the first, causing
# infinite recursion on any _va_save(VA_FILE, d) style call. We keep the
# two-argument helper under a distinct name, _va_write, and leave the
# one-argument _va_save(d) below unchanged. All two-arg call sites in this
# file now use _va_write.
def _va_write(path, data):
    _jsave(path, data)


def _fetch_bank_list(force=False):
    cached = _va_load(BANK_CACHE_FILE, {})
    now = time.time()
    if (not force) and cached and (now - float(cached.get("ts") or 0)) < _BANK_CACHE_TTL:
        return cached.get("banks") or []

    if not FLW_SECRET_KEY:
        return cached.get("banks") or []

    try:
        r = _http.get(f"{FLW_BASE_URL}/banks/{VA_COUNTRY}",
                      headers=_flw_headers(), timeout=20)
        resp = r.json() if r.content else {}
        if r.status_code < 300 and resp.get("status") == "success":
            banks = resp.get("data") or []
            with _BANK_CACHE_LOCK:
                _va_write(BANK_CACHE_FILE, {"ts": now, "country": VA_COUNTRY, "banks": banks})
            return banks
    except Exception as e:
        print(f"[VA BANKLIST] fetch failed: {e}")
    return cached.get("banks") or []


def _bank_code_valid(code):
    code = str(code or "").strip()
    if not code:
        return False
    banks = _fetch_bank_list()
    if not banks:
        return True
    return any(str(b.get("code", "")).strip() == code for b in banks)


@app.route("/api/banks/KE", methods=["GET"])
def api_banks_ke():
    banks = _fetch_bank_list(force=("refresh" in request.args))
    return jsonify({
        "success": True,
        "country": VA_COUNTRY,
        "banks": banks,
        "cached_at": _va_load(BANK_CACHE_FILE, {}).get("ts"),
    })


def _resolve_account(bank_code, account_number):
    bank_code = str(bank_code or "").strip()
    account_number = str(account_number or "").strip()
    if not bank_code or not account_number:
        return {"ok": False, "message": "bank_code and account_number required."}
    if not FLW_SECRET_KEY:
        return {"ok": False, "message": "Flutterwave keys not configured."}
    try:
        payload = {"account_number": account_number, "account_bank": bank_code}
        r = _http.post(f"{FLW_BASE_URL}/accounts/resolve", json=payload,
                       headers=_flw_headers(), timeout=20)
        resp = r.json() if r.content else {}
        if r.status_code < 300 and resp.get("status") == "success":
            data = resp.get("data") or {}
            return {
                "ok": True,
                "account_name": str(data.get("account_name") or "").strip(),
                "account_number": str(data.get("account_number") or account_number),
                "bank_code": bank_code,
            }
        return {"ok": False, "message": str(resp.get("message") or "Resolve failed")}
    except Exception as e:
        return {"ok": False, "message": str(e)}


@app.route("/api/payout/resolve", methods=["POST"])
def api_payout_resolve():
    data = request.get_json() or {}
    bank_code = str(data.get("bank_code") or "").strip()
    account_number = str(data.get("account_number") or "").strip()

    if not _bank_code_valid(bank_code):
        return jsonify({"success": False, "message": "Unknown bank_code."}), 400

    res = _resolve_account(bank_code, account_number)
    if not res.get("ok"):
        return jsonify({"success": False, "message": res.get("message")}), 502
    return jsonify({"success": True, "data": res})


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

        # === KYC_MATCH_ENFORCEMENT (ADDITIVE) ===
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
        # === END KYC_MATCH_ENFORCEMENT ===

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


def _va_all():
    d = _va_load(VA_FILE, {})
    return d if isinstance(d, dict) else {}


def _va_save(d):
    _va_write(VA_FILE, d)


def _va_get(wallet_addr):
    return _va_all().get(wallet_addr)


def _va_audit(row):
    rows = _va_load(VA_AUDIT_FILE, [])
    if not isinstance(rows, list):
        rows = []
    rows.append(row)
    _va_write(VA_AUDIT_FILE, rows)


def _va_credits_all():
    rows = _va_load(VA_CREDITS_FILE, [])
    return rows if isinstance(rows, list) else []


def _va_credit_find(tx_ref):
    for r in _va_credits_all():
        if r.get("tx_ref") == tx_ref:
            return r
    return None


def _va_credit_add(row):
    rows = _va_credits_all()
    rows.append(row)
    _va_write(VA_CREDITS_FILE, rows)


def _va_credit_update(tx_ref, **fields):
    rows = _va_credits_all()
    for r in rows:
        if r.get("tx_ref") == tx_ref:
            r.update(fields)
            _va_write(VA_CREDITS_FILE, rows)
            return r
    return None


def _va_inflow_today_kes(wallet_addr):
    today = datetime.now().strftime("%Y-%m-%d")
    total = 0.0
    count = 0
    for r in _va_credits_all():
        if r.get("wallet_address") != wallet_addr:
            continue
        if r.get("status") != "COMPLETED":
            continue
        if str(r.get("created_at", "")).startswith(today):
            total += float(r.get("amount_kes") or 0)
            count += 1
    return round(total, 2), count


def _va_inflow_lifetime_kes(wallet_addr):
    total = 0.0
    for r in _va_credits_all():
        if r.get("wallet_address") != wallet_addr:
            continue
        if r.get("status") != "COMPLETED":
            continue
        total += float(r.get("amount_kes") or 0)
    return round(total, 2)


def _va_check_inflow_limits(wallet_addr, amount_kes):
    if amount_kes < VA_MIN_KES:
        return False, f"Amount below minimum KES {VA_MIN_KES:.2f}."
    if amount_kes > VA_MAX_KES:
        return False, f"Amount above per-transaction cap KES {VA_MAX_KES:.2f}."
    today_kes, today_count = _va_inflow_today_kes(wallet_addr)
    if today_count + 1 > VA_MAX_PER_DAY:
        return False, f"Daily VA credit count exceeded ({VA_MAX_PER_DAY})."
    if today_kes + amount_kes > VA_DAILY_MAX_KES:
        return False, f"Would exceed today's VA inflow cap KES {VA_DAILY_MAX_KES:.2f}."
    lifetime = _va_inflow_lifetime_kes(wallet_addr)
    if lifetime + amount_kes > VA_LIFETIME_MAX_KES:
        return False, f"Would exceed lifetime VA inflow cap KES {VA_LIFETIME_MAX_KES:.2f}."
    return True, "OK"


@app.route("/api/va/create", methods=["POST"])
def api_va_create():
    if not VA_ENABLED:
        return jsonify({
            "success": False,
            "message": "Virtual Accounts are disabled (VA_ENABLED=0).",
        }), 503
    if not FLW_SECRET_KEY:
        return jsonify({"success": False, "message": "Flutterwave keys missing."}), 500

    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()

        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        existing = _va_get(wallet_addr)
        if existing and existing.get("status") == "ACTIVE":
            return jsonify({
                "success": True,
                "message": "Virtual account already exists.",
                "va": existing,
            })

        if KYC_REQUIRED:
            kyc = _kyc_get(wallet_addr)
            if not kyc or kyc.get("status") != "VERIFIED":
                return jsonify({
                    "success": False,
                    "message": "KYC must be verified before VA issuance.",
                    "kyc_status": (kyc or {}).get("status", "NOT_SUBMITTED"),
                }), 403
            full_name = kyc.get("full_name")
            phone     = kyc.get("phone")
            id_number = kyc.get("id_number")
            id_type   = kyc.get("id_type")
            dob       = kyc.get("dob")
        else:
            client = _client_by_wallet(wallet_addr) or {}
            full_name = client.get("name") or "PSC Customer"
            phone     = _normalize_phone(client.get("phone") or "")
            id_number = ""
            id_type   = ""
            dob       = ""

        if _name_in_sanctions(full_name):
            _compliance_flag_add({
                "at": _now(), "wallet": wallet_addr,
                "type": "SANCTIONS_HIT_VA", "name": full_name,
            })
            return jsonify({"success": False, "message": "Sanctions screen failed."}), 403

        try:
            payload = {
                "email": (data.get("email") or "customer@example.com"),
                "is_permanent": True,
                "bvn": id_number if VA_COUNTRY == "NG" else None,
                "phonenumber": phone or "",
                "firstname": str(full_name).split(" ")[0][:32] if full_name else "PSC",
                "lastname": (" ".join(str(full_name).split(" ")[1:]) or "Customer")[:32],
                "narration": f"PSC VA for {wallet_addr}",
            }
            payload = {k: v for k, v in payload.items() if v is not None}

            r = _http.post(f"{FLW_BASE_URL}/virtual-account-numbers",
                           json=payload, headers=_flw_headers(), timeout=25)
            resp = r.json() if r.content else {}
            if r.status_code >= 300 or resp.get("status") != "success":
                return jsonify({
                    "success": False,
                    "message": str(resp.get("message") or "Flutterwave VA creation failed"),
                }), 502

            vdata = resp.get("data") or {}
            va_record = {
                "wallet_address": wallet_addr,
                "va_id": str(vdata.get("id") or vdata.get("order_ref") or ""),
                "account_number": str(vdata.get("account_number") or ""),
                "bank_name": str(vdata.get("bank_name") or ""),
                "account_name": str(vdata.get("account_name") or full_name),
                "country": VA_COUNTRY,
                "currency": VA_CURRENCY,
                "status": "ACTIVE",
                "created_at": _now(),
                "expires_at": (datetime.now() + timedelta(days=VA_EXPIRY_DAYS)).strftime("%Y-%m-%d %H:%M:%S"),
                "kyc_snapshot": {
                    "full_name": full_name, "id_type": id_type,
                    "id_number_masked": ("*" * max(0, len(id_number) - 4) + id_number[-4:]) if id_number else "",
                    "dob": dob, "phone": phone,
                },
            }
            d = _va_all()
            d[wallet_addr] = va_record
            _va_save(d)

            _va_audit({
                "at": _now(), "wallet": wallet_addr,
                "action": "VA_CREATED",
                "va_id": va_record["va_id"],
                "account_number": va_record["account_number"],
                "bank_name": va_record["bank_name"],
            })

            return jsonify({"success": True, "va": va_record,
                            "message": "Virtual account created."})
        except Exception as e:
            return jsonify({"success": False, "message": str(e)}), 500
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/va/status", methods=["GET", "POST"])
def api_va_status():
    data = request.get_json(silent=True) or {}
    session_wallet = session.get("wallet", "")
    wallet_addr = str(data.get("wallet") or request.args.get("wallet") or session_wallet or "").strip()
    if not wallet_addr:
        return jsonify({"success": False, "message": "Wallet is required."}), 400
    va = _va_get(wallet_addr)
    if not va:
        return jsonify({"success": True, "va_status": "NOT_CREATED"})
    return jsonify({"success": True, "va_status": va.get("status"), "va": va})


@app.route("/api/va/close", methods=["POST"])
def api_va_close():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        wallet_addr = str(data.get("wallet") or session_wallet or "").strip()
        if not wallet_addr:
            return jsonify({"success": False, "message": "Wallet is required."}), 400
        if session_wallet and wallet_addr != session_wallet:
            return jsonify({"success": False, "message": "Wallet mismatch."}), 403

        d = _va_all()
        va = d.get(wallet_addr)
        if not va:
            return jsonify({"success": False, "message": "No VA found."}), 404
        if va.get("status") != "ACTIVE":
            return jsonify({"success": True, "va": va,
                            "message": f"Already {va.get('status')}"})

        pending = [r for r in _va_credits_all()
                   if r.get("wallet_address") == wallet_addr and r.get("status") == "PENDING"]
        if pending:
            return jsonify({
                "success": False,
                "message": f"{len(pending)} pending VA credit(s). Try later.",
            }), 409

        va["status"] = "CLOSED"
        va["closed_at"] = _now()
        d[wallet_addr] = va
        _va_save(d)

        _va_audit({"at": _now(), "wallet": wallet_addr,
                   "action": "VA_CLOSED", "va_id": va.get("va_id")})
        return jsonify({"success": True, "va": va, "message": "VA closed."})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


def _credit_wallet_from_va(wallet_addr, amount_kes, tx_ref, sender_name,
                           sender_bank, narration=""):
    existing = _va_credit_find(tx_ref)
    if existing and existing.get("status") == "COMPLETED":
        return True, "already-credited", existing

    ok, msg = _va_check_inflow_limits(wallet_addr, amount_kes)
    if not ok:
        _va_credit_add({
            "tx_ref": tx_ref, "wallet_address": wallet_addr,
            "amount_kes": amount_kes, "status": "REJECTED_LIMIT",
            "reason": msg, "created_at": _now(),
            "sender_name": sender_name, "sender_bank": sender_bank,
            "narration": narration,
        })
        _va_audit({"at": _now(), "wallet": wallet_addr, "action": "VA_CREDIT_REJECTED",
                   "tx_ref": tx_ref, "reason": msg, "amount_kes": amount_kes})
        return False, msg, None

    if amount_kes >= CBK_REPORT_THRESHOLD_KES:
        _compliance_flag_add({
            "at": _now(), "wallet": wallet_addr, "type": "LARGE_VA_CREDIT",
            "amount_kes": amount_kes, "tx_ref": tx_ref,
            "detail": "Exceeds CBK report threshold",
        })

    if _name_in_sanctions(sender_name):
        _compliance_flag_add({
            "at": _now(), "wallet": wallet_addr, "type": "SANCTIONS_SENDER",
            "sender_name": sender_name, "amount_kes": amount_kes, "tx_ref": tx_ref,
        })

    psc_amount = round(float(amount_kes) / PSC_TO_KES_RATE, 2)
    ok, msg, _wallet = _add_purchased_psc(
        wallet_addr, psc_amount, amount_kes,
        payment_reference=f"VA:{tx_ref}",
    )
    if not ok:
        _va_credit_add({
            "tx_ref": tx_ref, "wallet_address": wallet_addr,
            "amount_kes": amount_kes, "status": "FAILED_CREDIT",
            "reason": msg, "created_at": _now(),
            "sender_name": sender_name, "sender_bank": sender_bank,
            "narration": narration,
        })
        return False, msg, None

    row = {
        "tx_ref": tx_ref, "wallet_address": wallet_addr,
        "amount_kes": amount_kes, "credited_psc": psc_amount,
        "status": "COMPLETED", "created_at": _now(),
        "sender_name": sender_name, "sender_bank": sender_bank,
        "narration": narration, "credited_at": _now(),
    }
    _va_credit_add(row)

    _va_audit({
        "at": _now(), "wallet": wallet_addr, "action": "VA_CREDIT",
        "tx_ref": tx_ref, "amount_kes": amount_kes, "credited_psc": psc_amount,
        "sender_name": sender_name, "sender_bank": sender_bank,
    })

    _admin_ledger_add({
        "type": "VA_CREDIT",
        "wallet_address": wallet_addr,
        "tx_ref": tx_ref,
        "amount_kes": amount_kes,
        "credited_psc": psc_amount,
        "sender_name": sender_name,
        "sender_bank": sender_bank,
        "status": "COMPLETED",
        "time": _now(),
    })
    return True, "OK", row


@app.route("/webhooks/flutterwave_va", methods=["POST"])
def webhook_flutterwave_va():
    try:
        if not FLW_WEBHOOK_SECRET:
            return jsonify({"success": False, "message": "webhook secret not configured"}), 401
        sent = request.headers.get("verif-hash", "")
        if not hmac.compare_digest(sent, FLW_WEBHOOK_SECRET):
            return jsonify({"success": False, "message": "bad signature"}), 401

        body = request.get_json(silent=True) or {}
        event = str(body.get("event") or body.get("type") or "").strip().lower()
        d = body.get("data") or {}

        if event in ("virtualaccount.credit", "va.credit",
                     "charge.completed", "transfer.completed"):
            account_number = str(d.get("account_number") or "").strip()
            amount_kes = float(d.get("amount") or 0)
            currency = str(d.get("currency") or "").upper()
            tx_ref = str(d.get("tx_ref") or d.get("id") or uuid.uuid4().hex[:20]).strip()
            sender_name = str(d.get("sender_name") or d.get("customer", {}).get("name") or "").strip()
            sender_bank = str(d.get("sender_bank") or "").strip()
            narration = str(d.get("narration") or "").strip()

            if currency != VA_CURRENCY:
                return jsonify({"success": True, "message": "ignored non-KES"}), 200
            if not account_number or amount_kes <= 0:
                return jsonify({"success": True, "message": "ignored"}), 200

            wallet_addr = ""
            for w, va in _va_all().items():
                if str(va.get("account_number", "")).strip() == account_number:
                    wallet_addr = w
                    break
            if not wallet_addr:
                _va_audit({"at": _now(), "action": "VA_CREDIT_UNKNOWN_ACCOUNT",
                           "account_number": account_number, "amount_kes": amount_kes})
                return jsonify({"success": True, "message": "unknown VA"}), 200

            ok, msg, _row = _credit_wallet_from_va(
                wallet_addr, amount_kes, tx_ref, sender_name, sender_bank, narration
            )
            return jsonify({"success": ok, "message": msg}), 200

        if event in ("chargeback.completed", "va.reversal", "refund.completed",
                     "transfer.reversed"):
            tx_ref = str(d.get("tx_ref") or d.get("id") or "").strip()
            row = _va_credit_find(tx_ref)
            if row and row.get("status") == "COMPLETED":
                row["status"] = "REVERSED"
                row["reversed_at"] = _now()
                _va_write(VA_CREDITS_FILE, _va_credits_all())
                wallet_addr = row.get("wallet_address")
                psc = float(row.get("credited_psc") or 0)
                if wallet_addr and psc > 0:
                    try:
                        deduct_wallet_psc(wallet_addr, psc)
                    except Exception:
                        pass
                _va_audit({"at": _now(), "wallet": wallet_addr,
                           "action": "VA_REVERSAL", "tx_ref": tx_ref, "psc": psc})
                _admin_ledger_add({
                    "type": "VA_REVERSAL",
                    "wallet_address": wallet_addr,
                    "tx_ref": tx_ref,
                    "amount_psc": psc,
                    "status": "REVERSED",
                    "time": _now(),
                })
            return jsonify({"success": True}), 200

        return jsonify({"success": True, "message": "ignored"}), 200
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/va/limits/<wallet_addr>", methods=["GET"])
def api_va_limits(wallet_addr):
    today_kes, today_count = _va_inflow_today_kes(wallet_addr)
    lifetime = _va_inflow_lifetime_kes(wallet_addr)
    return jsonify({
        "success": True,
        "min_kes": VA_MIN_KES,
        "max_per_tx_kes": VA_MAX_KES,
        "daily_max_kes": VA_DAILY_MAX_KES,
        "daily_max_count": VA_MAX_PER_DAY,
        "lifetime_max_kes": VA_LIFETIME_MAX_KES,
        "today_kes": today_kes,
        "today_count": today_count,
        "lifetime_kes": lifetime,
    })


@app.route("/api/va/credits/<wallet_addr>", methods=["GET"])
def api_va_credits(wallet_addr):
    rows = [r for r in _va_credits_all() if r.get("wallet_address") == wallet_addr]
    return jsonify({"success": True, "credits": rows})


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

        if method == "bank":
            if not _bank_code_valid(bank_code):
                return {"ok": False, "status": 400, "gate": "bank_code_invalid",
                        "message": f"Unknown bank_code '{bank_code}'."}
            res = _resolve_account(bank_code, destination)
            if not res.get("ok"):
                return {"ok": False, "status": 502, "gate": "resolve_failed",
                        "message": f"Account resolution failed: {res.get('message')}"}
            resolved_name = (res.get("account_name") or "").strip().lower()
            expected_name = str((client or {}).get("name") or "").strip().lower()
            if expected_name:
                words_ok = any(
                    w in resolved_name for w in expected_name.split()
                    if len(w) >= 3
                )
                if not words_ok:
                    _compliance_flag_add({
                        "at": _now(), "wallet": wallet_addr,
                        "type": "NAME_MISMATCH_PAYOUT",
                        "expected": expected_name, "resolved": resolved_name,
                        "amount_kes": amount_kes,
                    })
                    return {
                        "ok": False, "status": 409, "gate": "name_mismatch",
                        "message": (f"Bank account name '{res.get('account_name')}' "
                                    f"does not match registered client name."),
                        "details": {"resolved_name": res.get("account_name"),
                                    "registered_name": expected_name},
                    }

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


@app.route("/api/admin/va/credits", methods=["GET"])
def api_admin_va_credits():
    sent = request.headers.get("X-PSC-Admin-Token", "")
    if not PSC_ADMIN_TOKEN or not hmac.compare_digest(sent, PSC_ADMIN_TOKEN):
        return jsonify({"success": False, "message": "forbidden"}), 403
    wallet = request.args.get("wallet")
    rows = _va_credits_all()
    if wallet:
        rows = [r for r in rows if r.get("wallet_address") == wallet]
    return jsonify({"success": True, "credits": rows})


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
# END VIRTUAL ACCOUNT (VA) + COMPLIANCE LAYER
# ============================================================


# ============================================================
# WALLET UPGRADE LAYER â€” ADDITIVE
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
    opts = []
    if WALLET_BANK_DEPOSIT_ENABLED:
        opts.append({
            "key": "banktransfer",
            "label": "Bank Transfer",
            "sub": "Deposit from any Kenyan bank",
            "gateways": [k for k in (("flutterwave" if FLW_SECRET_KEY else None),
                                     ("paystack" if (PAYSTACK_ENABLED and PAYSTACK_SECRET_KEY) else None)) if k],
        })
    if WALLET_CARD_DEPOSIT_ENABLED:
        opts.append({
            "key": "card",
            "label": "Card (Visa / Mastercard)",
            "sub": "Any credit or debit card",
            "gateways": [k for k in (("flutterwave" if FLW_SECRET_KEY else None),
                                     ("paystack" if (PAYSTACK_ENABLED and PAYSTACK_SECRET_KEY) else None)) if k],
        })
    if WALLET_MPESA_DEPOSIT_ENABLED:
        opts.append({
            "key": "mpesa",
            "label": "M-Pesa",
            "sub": "Safaricom M-Pesa",
            "gateways": [k for k in (("flutterwave" if FLW_SECRET_KEY else None),
                                     ("paystack" if (PAYSTACK_ENABLED and PAYSTACK_SECRET_KEY) else None)) if k],
        })
    if COINGATE_ENABLED and COINGATE_API_TOKEN:
        opts.append({
            "key": "crypto",
            "label": "Crypto (BTC, ETH, USDT-TRC20)",
            "sub": "Powered by CoinGate",
            "gateways": ["coingate"],
            "currencies": COINGATE_ALLOWED_CURRENCIES,
            "default_currency": COINGATE_DEFAULT_RECEIVE,
        })

    if MOONPAY_ENABLED and MOONPAY_PUBLISHABLE_KEY:
        opts.append({
            "key": "crypto_moonpay",
            "label": "Crypto Card (BTC, ETH, USDT, USDC)",
            "sub": "Powered by MoonPay - pay by card",
            "gateways": ["moonpay"],
            "currencies": [c.upper() for c in MOONPAY_ALLOWED_CRYPTOS],
            "default_currency": MOONPAY_BASE_CURRENCY.upper(),
            "fiat_currency": MOONPAY_CURRENCY_CODE.upper(),
        })
    return opts


@app.route("/api/wallet/deposit/initiate", methods=["POST"])
def api_wallet_deposit_initiate():
    try:
        data = request.get_json() or {}
        user = session.get("user")
        session_wallet = session.get("wallet", "")
        if not user or not session_wallet:
            return jsonify({"success": False,
                            "message": "Please log in to your account before depositing."}), 401

        address = str(data.get("wallet") or session_wallet or "").strip()
        if address != session_wallet:
            return jsonify({"success": False,
                            "message": "Wallet does not match the logged-in account."}), 403

        amount_kes = float(data.get("amount_kes") or 0)
        if amount_kes < 1:
            return jsonify({"success": False, "message": "amount_kes must be at least 1"}), 400

        if WALLET_DEPOSIT_MAX_KES > 0 and amount_kes > WALLET_DEPOSIT_MAX_KES + 1e-9:
            return jsonify({
                "success": False,
                "message": f"Single deposit exceeds cap KES {WALLET_DEPOSIT_MAX_KES:.2f}.",
                "max_deposit_kes": WALLET_DEPOSIT_MAX_KES,
            }), 400

        channel = str(data.get("channel") or "card").strip().lower()
        if channel not in ("card", "banktransfer", "bank", "mpesa"):
            channel = "card"

        gateway = str(data.get("gateway") or "").strip().lower()
        if gateway not in ("flutterwave", "paystack"):
            gateway = "flutterwave" if FLW_SECRET_KEY else ("paystack" if (PAYSTACK_ENABLED and PAYSTACK_SECRET_KEY) else "flutterwave")

        # ADDITIVE (Option C): target pocket.
        target = _normalize_credit_target(
            data.get("target") or data.get("credit_target") or "spendable"
        )

        _deposit_tx_ref = (
            ("PSC-PS-" if gateway == "paystack" else "PSC-") + uuid.uuid4().hex[:16]
        )

        _wallet_ops_add({
            "type": "DEPOSIT",
            "tx_ref": _deposit_tx_ref,
            "wallet_address": address,
            "amount_kes": round(amount_kes, 2),
            "channel": channel,
            "gateway": gateway,
            "target": target,
            "status": "INITIATED",
            "created_at": _now(),
        })

        # === DEPOSIT_SESSION_PROPAGATION_FIX ===
        # Snapshot the outer session before entering the nested
        # request context (which otherwise starts with an empty session).
        _saved_session = dict(session)
        _payload = {
            "wallet": address,
            "amount_kes": amount_kes,
            "gateway": gateway,
            "target": target,
            "redirect_url": data.get("redirect_url"),
        }

        # === DEPOSIT_WRAPPER_INLINE_FIX ===
        # Instead of nesting api_psc_topup_initiate() inside a new
        # request context (which loses the session), do the topup
        # inline on the current request. Same session throughout.
        #
        # === FIX #B ===
        # Removed unreachable dead code that used to sit after this
        # if/else. Both branches return, so anything below them was
        # never executed and would have crashed with NameError if ever
        # reached (undefined `resp`).
        if gateway == "paystack":
            if not PAYSTACK_ENABLED:
                return jsonify({"success": False, "message": "Paystack is disabled (PAYSTACK_ENABLED=0)."}), 503
            if not PAYSTACK_SECRET_KEY:
                return jsonify({"success": False, "message": "Paystack keys not configured in .env"}), 500
            client = get_client_by_phone(session.get("verified_phone", ""))
            if not client:
                return jsonify({"success": False, "message": "No registered account found for your phone number."}), 404
            if str(client.get("wallet_address", "")).strip() != address:
                return jsonify({"success": False, "message": "Your verified phone does not belong to this wallet."}), 403
            amount_subunit = int(round(amount_kes * 100))
            tx_ref = _deposit_tx_ref
            expected_psc = round(amount_kes / PSC_TO_KES_RATE, 2)
            _ps_payment_add({
                "tx_ref": tx_ref, "wallet_address": address,
                "amount_kes": round(amount_kes, 2), "expected_psc": expected_psc,
                "status": "PENDING", "provider": "paystack",
                "ps_reference": None, "created_at": _now(),
                "verified_at": None, "credited_psc": 0.0, "target": target,
            })
            payload = {
                "email": client.get("email") or "customer@example.com",
                "amount": amount_subunit,
                "currency": PAYSTACK_CURRENCY,
                "reference": tx_ref,
                "callback_url": data.get("redirect_url") or (request.url_root.rstrip("/") + "/psc_topup_return"),
                "metadata": {"wallet": address, "target": target},
            }
            r = _http.post(f"{PAYSTACK_BASE_URL}/transaction/initialize", json=payload, headers=_ps_headers(), timeout=20)
            resp_json = r.json() if r.content else {}
            if r.status_code >= 300 or not resp_json.get("status"):
                _ps_payment_update(tx_ref, status="FAILED", error=str(resp_json.get("message") or r.text)[:300])
                return jsonify({"success": False, "message": resp_json.get("message") or "Paystack error"}), 502
            pdata = resp_json.get("data") or {}
            return jsonify({
                "success": True, "tx_ref": tx_ref,
                "checkout_url": pdata.get("authorization_url"),
                "access_code": pdata.get("access_code"),
                "reference": pdata.get("reference") or tx_ref,
                "amount_kes": round(amount_kes, 2),
                "expected_psc": expected_psc,
                "gateway": "paystack", "target": target,
                "message": "Open the checkout link to complete payment.",
            })
        else:
            # Flutterwave â€” inline, using the CURRENT request/session
            if not FLW_SECRET_KEY:
                return jsonify({"success": False, "message": "Flutterwave keys not configured in .env"}), 500
            client = get_client_by_phone(session.get("verified_phone", ""))
            if not client:
                return jsonify({"success": False, "message": "No registered account found for your phone number."}), 404
            if str(client.get("wallet_address", "")).strip() != address:
                return jsonify({"success": False, "message": "Your verified phone does not belong to this wallet."}), 403
            tx_ref = _deposit_tx_ref
            expected_psc = round(amount_kes / PSC_TO_KES_RATE, 2)
            _payment_add({
                "tx_ref": tx_ref, "wallet_address": address,
                "amount_kes": round(amount_kes, 2), "expected_psc": expected_psc,
                "status": "PENDING", "provider": "flutterwave",
                "flw_tx_id": None, "created_at": _now(),
                "verified_at": None, "credited_psc": 0.0, "target": target,
            })
            payload = {
                "tx_ref": tx_ref,
                "amount": str(round(amount_kes, 2)),
                "currency": "KES",
                "redirect_url": data.get("redirect_url") or request.url_root.rstrip("/") + "/psc_topup_return",
                "payment_options": "card,mpesa,banktransfer,ussd",
                "customer": {
                    "email": client.get("email") or "customer@example.com",
                    "phonenumber": client.get("phone") or session.get("verified_phone", ""),
                    "name": client.get("name") or "PSC Customer",
                },
                "customizations": {"title": "PSC Top-Up", "description": f"Buy {expected_psc} PSC for KES {amount_kes:.2f}"},
            }
            r = _http.post(f"{FLW_BASE_URL}/payments", json=payload, headers=_flw_headers(), timeout=20)
            resp_json = r.json() if r.content else {}
            if r.status_code >= 300 or resp_json.get("status") != "success":
                _payment_update(tx_ref, status="FAILED", error=str(resp_json.get("message") or r.text)[:300])
                return jsonify({"success": False, "message": resp_json.get("message") or "Flutterwave error"}), 502
            return jsonify({
                "success": True, "tx_ref": tx_ref,
                "checkout_url": resp_json["data"]["link"],
                "amount_kes": round(amount_kes, 2),
                "expected_psc": expected_psc,
                "gateway": "flutterwave", "target": target,
                "message": "Open the checkout link to complete payment.",
            })
        # === END DEPOSIT_WRAPPER_INLINE_FIX ===
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/deposit/verify", methods=["POST"])
def api_wallet_deposit_verify():
    try:
        data = request.get_json() or {}
        tx_ref = str(data.get("tx_ref") or "").strip()
        gateway = str(data.get("gateway") or "flutterwave").strip().lower()
                # === FIX 7: use the current request context; test_request_context
        # wipes the session and breaks authenticated credit. ===
        if gateway == "paystack":
            resp = api_psc_topup_verify_ps()
        else:
            resp = api_psc_topup_verify()
        # === END FIX 7 ===

        body = resp[0].get_json() if isinstance(resp, tuple) else resp.get_json()
        status_code = resp[1] if isinstance(resp, tuple) else resp.status_code

        if body.get("success") and tx_ref:
            with _WALLET_OPS_LOCK:
                rows = _wallet_ops_all()
                for r in rows:
                    if r.get("type") == "DEPOSIT" and r.get("tx_ref") == tx_ref:
                        r["status"] = "COMPLETED"
                        r["verified_at"] = _now()
                        break
                _jsave(WALLET_OPS_FILE, rows)

        return jsonify(body), status_code
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/wallet/deposit/history/<wallet_addr>", methods=["GET"])
def api_wallet_deposit_history(wallet_addr):
    rows = [r for r in _wallet_ops_all()
            if r.get("type") == "DEPOSIT" and r.get("wallet_address") == wallet_addr]
    # ADDITIVE (Option C): per-target breakdown.
    by_target = {"spendable": 0.0, "savings": 0.0, "deposit": 0.0}
    for r in rows:
        if r.get("status") != "COMPLETED":
            continue
        t = _normalize_credit_target(r.get("target") or "spendable")
        by_target[t] = round(by_target.get(t, 0.0) + float(r.get("amount_kes") or 0), 2)
    return jsonify({
        "success": True,
        "deposits": rows,
        "today_kes": _wallet_deposit_today_kes(wallet_addr),
        "max_deposit_kes": WALLET_DEPOSIT_MAX_KES,
        "by_target_kes": by_target,
        "psc_to_kes_rate": PSC_TO_KES_RATE,
    })


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

        available = round(float(wallet.get("wallet_psc", 0) or 0), 2)
        if amount_psc > available - 1.00 + 1e-9:
            return jsonify({
                "success": False,
                "message": (f"At least 1.00 PSC must remain. Available {available:.2f} PSC. "
                            f"Maximum withdrawable {max(0.0, available - 1.00):.2f} PSC."),
                "wallet_psc": available,
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
        ok, msg, _w = _wallet_hold_withdrawal(wallet_addr, amount_psc, withdrawal_id)
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

        if PAYOUTS_LIVE:
            ok, info, err = _flw_transfer(row)
            if not ok:
                return jsonify({"success": False,
                                "message": err or "Flutterwave transfer failed",
                                "withdrawal": _wq_find(wid)}), 502
            transfer_id = (info.get("data") or {}).get("id") if isinstance(info, dict) else None
            _wq_update(wid, status="PAID", settled_at=_now(),
                       transfer_id=transfer_id, mode="auto", flw_response=info)
        else:
            _wq_update(wid, status="PAID", settled_at=_now(),
                       mpesa_code=code, mode="manual")

        _wallet_release_or_settle(wallet_addr, amount_psc, wid, "PAID")
        _ledger_update(wid, status="PAID", settled_at=_now(),
                       mode=("auto" if PAYOUTS_LIVE else "manual"), reference=code)
        _audit_add({
            "withdrawal_id": wid, "amount_kes": amount_kes,
            "method": row.get("method"),
            "at": _now(), "mode": ("auto" if PAYOUTS_LIVE else "manual"),
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
# END WALLET UPGRADE LAYER
# ============================================================


# ============================================================
# SAVINGS SUB-BALANCE â€” ADDITIVE
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
# ADDITIVE (Option C) â€” DEPOSIT PSC POCKET (HOLD-ONLY)
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
    """Move spendable PSC -> deposit_psc (hold-only pocket)."""
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
    """Move deposit_psc (hold-only) -> spendable wallet_psc."""
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


# ============================================================
# END DEPOSIT PSC POCKET (Option C)
# ============================================================


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
            # === GAP FIX #1 ===
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

    actions = [
        {
            "key": "deposit",
            "label": "Add Money",
            "icon": "âž•",
            "endpoint": "/api/wallet/deposit/initiate",
            "method": "POST",
            "fields": ["amount_kes", "channel", "gateway", "target"],
            "channels": _wallet_ui_deposit_options(),
            "targets": [
                {"key": "spendable", "label": "Spendable PSC",
                 "hint": "Used for shopping."},
                {"key": "savings",   "label": "Savings PSC",
                 "hint": "Parked; withdrawable only."},
                {"key": "deposit",   "label": "Deposit PSC",
                 "hint": "Hold-only; not spent by shopping."},
            ],
            "max_kes": WALLET_DEPOSIT_MAX_KES,
            "hint": "Deposit from any bank, card or M-Pesa.",
        },
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
            "icon": "ðŸ§Š",
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
            "icon": "ðŸ§Š",
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
            "icon": "ðŸŽ",
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
        # === GAP FIX #1 ===
        "min_balance_to_shop": MIN_BALANCE_TO_SHOP,
        "updated_at": _now(),
    })


# ============================================================
# END SAVINGS SUB-BALANCE
# ============================================================


# ============================================================
# PAYMENT LINKS - ADDITIVE
# ============================================================

PAYMENT_LINKS_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "payment_links.json"
)

_PAYMENT_LINKS_LOCK = threading.Lock()

PAYMENT_LINK_DEFAULT_TTL_HOURS = int(
    os.getenv("PAYMENT_LINK_DEFAULT_TTL_HOURS", "168") or 168
)
PAYMENT_LINK_MIN_KES = float(os.getenv("PAYMENT_LINK_MIN_KES", "10") or 10)
PAYMENT_LINK_MAX_KES = float(os.getenv("PAYMENT_LINK_MAX_KES", "0") or 0)


def _payment_links_all():
    d = _jload(PAYMENT_LINKS_FILE, {})
    return d if isinstance(d, dict) else {}


def _payment_link_save(d):
    _jsave(PAYMENT_LINKS_FILE, d)


def _payment_link_get(token):
    return _payment_links_all().get(str(token or "").strip())


def _payment_link_upsert(token, row):
    with _PAYMENT_LINKS_LOCK:
        d = _payment_links_all()
        d[str(token)] = row
        _payment_link_save(d)


def _payment_link_is_usable(row, now=None):
    if not row:
        return False, "Link not found."
    if row.get("status") != "ACTIVE":
        return False, "Link is " + str(row.get("status")) + "."
    now = now or datetime.now()
    exp = row.get("expires_at")
    if exp:
        try:
            if datetime.strptime(exp, "%Y-%m-%d %H:%M:%S") < now:
                return False, "Link has expired."
        except Exception:
            pass
    cap_psc = float(row.get("cap_psc") or 0)
    if cap_psc > 0:
        collected = float(row.get("collected_psc") or 0)
        if collected >= cap_psc - 1e-9:
            return False, "This payment link has reached its collection cap."
    return True, "OK"


@app.route("/api/payment_link/create", methods=["POST"])
def api_payment_link_create():
    try:
        data = request.get_json() or {}
        session_wallet = session.get("wallet", "")
        sent_token = request.headers.get("X-PSC-Admin-Token", "")
        is_admin = bool(PSC_ADMIN_TOKEN) and hmac.compare_digest(sent_token, PSC_ADMIN_TOKEN)

        if is_admin:
            wallet_addr = str(data.get("wallet") or "").strip()
            if not wallet_addr:
                return jsonify({"success": False,
                                "message": "wallet is required for admin-created links."}), 400
        else:
            wallet_addr = str(session_wallet or "").strip()
            if not wallet_addr:
                return jsonify({"success": False,
                                "message": "Please log in first to create a payment link."}), 401

        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found."}), 404

        amount_kes = 0.0
        if data.get("amount_kes") not in (None, "", 0, "0"):
            try:
                amount_kes = round(float(data.get("amount_kes")), 2)
            except (TypeError, ValueError):
                return jsonify({"success": False, "message": "amount_kes must be a number."}), 400
            if amount_kes < PAYMENT_LINK_MIN_KES:
                return jsonify({"success": False,
                                "message": "Minimum amount is KES %.2f." % PAYMENT_LINK_MIN_KES}), 400
            if PAYMENT_LINK_MAX_KES > 0 and amount_kes > PAYMENT_LINK_MAX_KES + 1e-9:
                return jsonify({"success": False,
                                "message": "Maximum amount is KES %.2f." % PAYMENT_LINK_MAX_KES}), 400

        target = _normalize_credit_target(data.get("target") or "spendable")

        gateway = str(data.get("gateway") or "flutterwave").strip().lower()
        if gateway not in ("flutterwave", "paystack"):
            gateway = "flutterwave"

        try:
            ttl_hours = int(data.get("ttl_hours") or PAYMENT_LINK_DEFAULT_TTL_HOURS)
        except (TypeError, ValueError):
            ttl_hours = PAYMENT_LINK_DEFAULT_TTL_HOURS
        if ttl_hours < 1:
            ttl_hours = PAYMENT_LINK_DEFAULT_TTL_HOURS

        cap_psc = 0.0
        if is_admin and data.get("cap_psc") not in (None, "", 0, "0"):
            try:
                cap_psc = round(float(data.get("cap_psc")), 2)
            except (TypeError, ValueError):
                cap_psc = 0.0

        token = uuid.uuid4().hex[:24]
        now = datetime.now()
        row = {
            "token": token,
            "wallet_address": wallet_addr,
            "amount_kes": amount_kes,
            "target": target,
            "gateway": gateway,
            "note": str(data.get("note") or "").strip()[:120],
            "status": "ACTIVE",
            "created_at": now.strftime("%Y-%m-%d %H:%M:%S"),
            "created_by": "admin" if is_admin else "user",
            "expires_at": (now + timedelta(hours=ttl_hours)).strftime("%Y-%m-%d %H:%M:%S"),
            "cap_psc": cap_psc,
            "collected_psc": 0.0,
            "collected_kes": 0.0,
            "payments": [],
        }
        _payment_link_upsert(token, row)

        # Use auto-share tunnel URL if available; fall back to request host.
        try:
            base = auto_share.public_base(fallback=request.url_root).rstrip("/")
        except Exception:
            base = request.url_root.rstrip("/")
        public_url = base + "/pay/" + token

        return jsonify({
            "success": True,
            "token": token,
            "url": public_url,
            "link": row,
            "psc_to_kes_rate": PSC_TO_KES_RATE,
            "message": "Payment link created.",
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/payment_link/<token>", methods=["GET"])
def api_payment_link_get(token):
    try:
        row = _payment_link_get(token)
        usable, reason = _payment_link_is_usable(row)
        if not row:
            return jsonify({"success": False, "message": reason}), 404

        wallet_addr = row.get("wallet_address", "")
        client = _client_by_wallet(wallet_addr) or {}
        wallet_short = wallet_addr[:8] + "..." + wallet_addr[-6:] if wallet_addr else ""

        return jsonify({
            "success": True,
            "usable": usable,
            "reason": reason,
            "link": {
                "token": token,
                "amount_kes": row.get("amount_kes", 0),
                "target": row.get("target", "spendable"),
                "gateway": row.get("gateway", "flutterwave"),
                "note": row.get("note", ""),
                "status": row.get("status"),
                "expires_at": row.get("expires_at"),
                "created_at": row.get("created_at"),
            },
            "recipient": {
                "name": client.get("name", "") or "PSC Merchant",
                "wallet_short": wallet_short,
            },
            "limits": {
                "min_kes": PAYMENT_LINK_MIN_KES,
                "max_kes": PAYMENT_LINK_MAX_KES,
            },
            "psc_to_kes_rate": PSC_TO_KES_RATE,
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500



# === ADDITIVE: payment-link verify helper ===
def _flw_verify_by_reference(tx_ref):
    if not FLW_SECRET_KEY:
        return False, 'Flutterwave keys not configured'
    try:
        r = _http.get(
            f"{FLW_BASE_URL}/transactions/verify_by_reference",
            params={'tx_ref': tx_ref},
            headers=_flw_headers(),
            timeout=20,
        )
        resp = r.json() if r.content else {}
        if r.status_code >= 300 or resp.get('status') != 'success':
            return False, resp.get('message') or 'verify_by_reference failed'
        return True, resp.get('data') or {}
    except Exception as e:
        return False, str(e)
# === END ADDITIVE ===

# === ADDITIVE: payment-link verify (client-side return handler) ===
@app.route("/api/payment_link/verify", methods=["POST"])
def api_payment_link_verify_client():
    try:
        data = request.get_json() or {}
        tx_ref = str(data.get("tx_ref") or "").strip()
        if not tx_ref:
            return jsonify({"success": False, "message": "tx_ref required"}), 400
        row = _payment_find(tx_ref)
        if not row:
            return jsonify({"success": False, "message": "Payment not found"}), 404
        st = str(row.get("status") or "").upper()
        if st == "COMPLETED":
            return jsonify({"success": True, "message": "Already completed", "status": "COMPLETED", "payment": row})
        if st == "AWAITING_APPROVAL":
            return jsonify({"success": True, "message": "Awaiting admin approval", "status": "AWAITING_APPROVAL", "payment": row})
        if st in ("FAILED", "REJECTED"):
            return jsonify({"success": False, "message": "Payment failed/rejected", "status": st, "payment": row}), 400
        ok, info = _flw_verify_by_reference(tx_ref)
        if not ok:
            _payment_update(tx_ref, status="FAILED", error=str(info)[:300])
            return jsonify({"success": False, "message": str(info), "status": "FAILED"}), 400
        got_status = str(info.get("status") or "").lower()
        got_amount = float(info.get("amount") or 0)
        got_currency = str(info.get("currency") or "").upper()
        if got_status != "successful":
            _payment_update(tx_ref, status="FAILED", error="provider status=" + got_status)
            return jsonify({"success": False, "message": "Provider status: " + got_status, "status": "FAILED"}), 400
        if got_currency != "KES":
            _payment_update(tx_ref, status="FAILED", error="currency=" + got_currency)
            return jsonify({"success": False, "message": "Currency mismatch", "status": "FAILED"}), 400
        if got_amount + 0.01 < float(row.get("amount_kes") or 0):
            _payment_update(tx_ref, status="FAILED", error="amount below expected")
            return jsonify({"success": False, "message": "Amount less than expected", "status": "FAILED"}), 400
        _payment_update(tx_ref, status="AWAITING_APPROVAL", flw_tx_id=info.get("id"), verified_at=_now(), error="Awaiting admin approval")
        return jsonify({"success": True, "message": "Payment confirmed by Flutterwave. Awaiting admin approval.", "status": "AWAITING_APPROVAL", "payment": _payment_find(tx_ref)})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500
# === END ADDITIVE ===

@app.route("/pay/<token>", methods=["GET"])
def pay_link_page(token):
    row = _payment_link_get(token)
    usable, reason = _payment_link_is_usable(row)

    wallet_addr = (row or {}).get("wallet_address", "")
    client = _client_by_wallet(wallet_addr) or {}
    recipient_name = client.get("name", "") or "PSC Merchant"
    wallet_short = wallet_addr[:8] + "..." + wallet_addr[-6:] if wallet_addr else ""
    fixed_amount = float((row or {}).get("amount_kes") or 0)
    target = (row or {}).get("target", "spendable")
    gateway = (row or {}).get("gateway", "flutterwave")
    note = (row or {}).get("note", "")

    html = render_template_string(
        PAY_LINK_TEMPLATE,
        token=token,
        usable=usable,
        reason=reason,
        recipient_name=recipient_name,
        wallet_short=wallet_short,
        fixed_amount=fixed_amount,
        target=target,
        gateway=gateway,
        note=note,
        min_kes=PAYMENT_LINK_MIN_KES,
        max_kes=PAYMENT_LINK_MAX_KES,
        psc_rate=PSC_TO_KES_RATE,
    )
    return html


@app.route("/api/payment_link/<token>/initiate", methods=["POST"])
def api_payment_link_initiate(token):
    try:
        row = _payment_link_get(token)
        usable, reason = _payment_link_is_usable(row)
        if not usable:
            return jsonify({"success": False, "message": reason}), 400

        data = request.get_json() or {}

        fixed_amount = float(row.get("amount_kes") or 0)
        if fixed_amount > 0:
            amount_kes = round(fixed_amount, 2)
        else:
            try:
                amount_kes = round(float(data.get("amount_kes") or 0), 2)
            except (TypeError, ValueError):
                amount_kes = 0.0

        if amount_kes < PAYMENT_LINK_MIN_KES:
            return jsonify({"success": False,
                            "message": "Minimum is KES %.2f." % PAYMENT_LINK_MIN_KES}), 400
        if PAYMENT_LINK_MAX_KES > 0 and amount_kes > PAYMENT_LINK_MAX_KES + 1e-9:
            return jsonify({"success": False,
                            "message": "Maximum is KES %.2f." % PAYMENT_LINK_MAX_KES}), 400

        wallet_addr = row["wallet_address"]
        wallet = get_wallet(wallet_addr)
        if not wallet:
            return jsonify({"success": False, "message": "Recipient wallet not found."}), 404

        cap_psc = float(row.get("cap_psc") or 0)
        if cap_psc > 0:
            remaining_psc = cap_psc - float(row.get("collected_psc") or 0)
            if remaining_psc <= 0:
                return jsonify({"success": False,
                                "message": "This payment link has reached its cap."}), 400
            if amount_kes / PSC_TO_KES_RATE > remaining_psc + 1e-9:
                return jsonify({
                    "success": False,
                    "message": "Only %.2f PSC (KES %.2f) can still be collected on this link." % (
                        remaining_psc, remaining_psc * PSC_TO_KES_RATE),
                    "remaining_psc": round(remaining_psc, 2),
                }), 400

        target = _normalize_credit_target(row.get("target") or "spendable")
        gateway = str(row.get("gateway") or "flutterwave").strip().lower()

        payer_name = str(data.get("payer_name") or "").strip()[:80]
        payer_email = str(data.get("payer_email") or "").strip()
        payer_phone = str(data.get("payer_phone") or "").strip()

        if not payer_email:
            payer_email = "payer@example.com"

        expected_psc = round(amount_kes / PSC_TO_KES_RATE, 2)

        if gateway == "flutterwave":
            if not FLW_SECRET_KEY:
                return jsonify({"success": False,
                                "message": "Flutterwave not configured."}), 500
            tx_ref = "PSC-LNK-" + uuid.uuid4().hex[:16]
            _payment_add({
                "tx_ref": tx_ref,
                "wallet_address": wallet_addr,
                "amount_kes": amount_kes,
                "expected_psc": expected_psc,
                "status": "PENDING",
                "provider": "flutterwave",
                "flw_tx_id": None,
                "created_at": _now(),
                "verified_at": None,
                "credited_psc": 0.0,
                "target": target,
                "via_link": token,
                "payer_name": payer_name,
                "payer_email": payer_email,
                "payer_phone": payer_phone,
            })

            base = request.url_root.rstrip("/")
            payload = {
                "tx_ref": tx_ref,
                "amount": str(amount_kes),
                "currency": "KES",
                "redirect_url": base + "/pay/" + token + "?tx_ref=" + tx_ref,
                "payment_options": "card,mpesa,banktransfer,ussd",
                "customer": {
                    "email": payer_email,
                    "phonenumber": payer_phone or "",
                    "name": payer_name or "PSC Payer",
                },
                "customizations": {
                    "title": "PSC Payment Link",
                    "description": "Pay %.2f PSC (KES %.2f)" % (expected_psc, amount_kes),
                },
            }
            r = _http.post(FLW_BASE_URL + "/payments", json=payload,
                           headers=_flw_headers(), timeout=20)
            resp = r.json() if r.content else {}
            if r.status_code >= 300 or resp.get("status") != "success":
                _payment_update(tx_ref, status="FAILED",
                                error=str(resp.get("message") or r.text)[:300])
                return jsonify({"success": False,
                                "message": resp.get("message") or "Flutterwave error"}), 502

            return jsonify({
                "success": True,
                "tx_ref": tx_ref,
                "gateway": "flutterwave",
                "checkout_url": resp["data"]["link"],
                "amount_kes": amount_kes,
                "expected_psc": expected_psc,
                "target": target,
            })

        if gateway == "paystack":
            if not PAYSTACK_ENABLED or not PAYSTACK_SECRET_KEY:
                return jsonify({"success": False,
                                "message": "Paystack not enabled/configured."}), 500
            tx_ref = "PSC-LNK-PS-" + uuid.uuid4().hex[:16]
            _ps_payment_add({
                "tx_ref": tx_ref,
                "wallet_address": wallet_addr,
                "amount_kes": amount_kes,
                "expected_psc": expected_psc,
                "status": "PENDING",
                "provider": "paystack",
                "ps_reference": None,
                "created_at": _now(),
                "verified_at": None,
                "credited_psc": 0.0,
                "target": target,
                "via_link": token,
                "payer_name": payer_name,
                "payer_email": payer_email,
                "payer_phone": payer_phone,
            })
            base = request.url_root.rstrip("/")
            payload = {
                "email": payer_email,
                "amount": int(round(amount_kes * 100)),
                "currency": PAYSTACK_CURRENCY,
                "reference": tx_ref,
                "callback_url": base + "/pay/" + token + "?tx_ref=" + tx_ref,
                "metadata": {
                    "wallet": wallet_addr,
                    "target": target,
                    "via_link": token,
                    "payer_name": payer_name,
                    "payer_phone": payer_phone,
                },
            }
            r = _http.post(PAYSTACK_BASE_URL + "/transaction/initialize",
                           json=payload, headers=_ps_headers(), timeout=20)
            resp = r.json() if r.content else {}
            if r.status_code >= 300 or not resp.get("status"):
                _ps_payment_update(tx_ref, status="FAILED",
                                   error=str(resp.get("message") or r.text)[:300])
                return jsonify({"success": False,
                                "message": resp.get("message") or "Paystack error"}), 502
            pdata = resp.get("data") or {}
            return jsonify({
                "success": True,
                "tx_ref": tx_ref,
                "gateway": "paystack",
                "checkout_url": pdata.get("authorization_url"),
                "access_code": pdata.get("access_code"),
                "reference": pdata.get("reference") or tx_ref,
                "amount_kes": amount_kes,
                "expected_psc": expected_psc,
                "target": target,
            })

        return jsonify({"success": False, "message": "Unknown gateway."}), 400
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


def _payment_link_recompute(token):
    row = _payment_link_get(token)
    if not row:
        return None
    wallet_addr = row.get("wallet_address")
    collected_psc = 0.0
    collected_kes = 0.0
    tx_refs = []

    for p in _payments_all():
        if p.get("via_link") != token:
            continue
        if p.get("wallet_address") != wallet_addr:
            continue
        if p.get("status") == "COMPLETED":
            collected_psc += float(p.get("credited_psc") or 0)
            collected_kes += float(p.get("amount_kes") or 0)
            tx_refs.append(p.get("tx_ref"))

    try:
        for p in _ps_payments_all():
            if p.get("via_link") != token:
                continue
            if p.get("wallet_address") != wallet_addr:
                continue
            if p.get("status") == "COMPLETED":
                collected_psc += float(p.get("credited_psc") or 0)
                collected_kes += float(p.get("amount_kes") or 0)
                tx_refs.append(p.get("tx_ref"))
    except Exception:
        pass

    row["collected_psc"] = round(collected_psc, 2)
    row["collected_kes"] = round(collected_kes, 2)
    row["payments"] = tx_refs

    cap_psc = float(row.get("cap_psc") or 0)
    if cap_psc > 0 and collected_psc >= cap_psc - 1e-9:
        row["status"] = "FULFILLED"

    _payment_link_upsert(token, row)
    return row


@app.route("/api/payment_link/list/<wallet_addr>", methods=["GET"])
def api_payment_link_list(wallet_addr):
    try:
        wallet_addr = str(wallet_addr or "").strip()
        session_wallet = session.get("wallet", "")
        sent_token = request.headers.get("X-PSC-Admin-Token", "")
        is_admin = bool(PSC_ADMIN_TOKEN) and hmac.compare_digest(sent_token, PSC_ADMIN_TOKEN)

        if not is_admin and session_wallet != wallet_addr:
            return jsonify({"success": False, "message": "Not allowed."}), 403

        all_links = _payment_links_all()
        rows = []
        for tok, row in all_links.items():
            if row.get("wallet_address") != wallet_addr:
                continue
            fresh = _payment_link_recompute(tok) or row
            usable, reason = _payment_link_is_usable(fresh)
            r = dict(fresh)
            r["usable"] = usable
            r["reason"] = reason
            try:
                _base = auto_share.public_base(fallback=request.url_root).rstrip("/")
            except Exception:
                _base = request.url_root.rstrip("/")
            r["url"] = _base + "/pay/" + tok
            rows.append(r)

        rows.sort(key=lambda x: x.get("created_at", ""), reverse=True)
        return jsonify({"success": True, "links": rows})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/payment_link/<token>/revoke", methods=["POST"])
def api_payment_link_revoke(token):
    try:
        row = _payment_link_get(token)
        if not row:
            return jsonify({"success": False, "message": "Link not found."}), 404

        session_wallet = session.get("wallet", "")
        sent_token = request.headers.get("X-PSC-Admin-Token", "")
        is_admin = bool(PSC_ADMIN_TOKEN) and hmac.compare_digest(sent_token, PSC_ADMIN_TOKEN)

        if not is_admin and row.get("wallet_address") != session_wallet:
            return jsonify({"success": False, "message": "Not allowed."}), 403

        row["status"] = "REVOKED"
        row["revoked_at"] = _now()
        _payment_link_upsert(token, row)
        return jsonify({"success": True, "link": row, "message": "Link revoked."})
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


PAY_LINK_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Pay PSC Merchant</title>
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<style>
  *{box-sizing:border-box}
  body{margin:0;font-family:'Segoe UI',Tahoma,Verdana,sans-serif;background:#f5f6fa;min-height:100vh;display:flex;align-items:center;justify-content:center;padding:20px}
  .card{background:#fff;border-radius:16px;box-shadow:0 12px 40px rgba(0,0,0,.12);max-width:440px;width:100%;padding:28px}
  h1{margin:0 0 6px;font-size:1.3rem;color:#1a1a2e}
  .sub{color:#666;font-size:.9rem;margin-bottom:18px}
  .rec{background:#f0f4ff;border-left:4px solid #667eea;padding:10px 14px;border-radius:8px;margin-bottom:18px;font-size:.9rem}
  .rec b{color:#1a1a2e}
  label{display:block;font-size:.85rem;font-weight:600;color:#334155;margin:12px 0 4px}
  input{width:100%;padding:12px 14px;border:2px solid #e5e7eb;border-radius:10px;font-size:1rem}
  input:focus{outline:none;border-color:#667eea}
  .btn{width:100%;padding:14px;background:linear-gradient(135deg,#667eea,#764ba2);color:#fff;border:none;border-radius:10px;font-size:1rem;font-weight:700;cursor:pointer;margin-top:18px}
  .btn:hover{opacity:.93}
  .btn:disabled{background:#999;cursor:not-allowed}
  .msg{margin-top:14px;padding:10px 14px;border-radius:8px;font-size:.9rem;display:none}
  .err{background:#fef2f2;color:#b91c1c;border:1px solid #fecaca;display:block}
  .ok{background:#ecfdf5;color:#065f46;border:1px solid #a7f3d0;display:block}
  .amount-note{font-size:.8rem;color:#64748b;margin-top:4px}
  .lock{background:#fef3c7;color:#92400e;padding:12px 14px;border-radius:8px;font-size:.9rem}
  .powered{margin-top:18px;text-align:center;font-size:.78rem;color:#94a3b8}
  .powered b{color:#667eea}
</style>
</head>
<body>
  <div class="card">
    {% if not usable %}
      <h1>Payment link unavailable</h1>
      <div class="lock">{{ reason }}</div>
    {% else %}
      <h1>Pay {{ recipient_name }}</h1>
      <div class="sub">Secure PSC deposit &middot; 1 PSC = KES {{ psc_rate }}</div>
      <div class="rec">
        <div>Paying to: <b>{{ recipient_name }}</b></div>
        <div>Wallet: <b>{{ wallet_short }}</b></div>
        {% if note %}<div style="margin-top:6px;color:#475569;">Note: {{ note }}</div>{% endif %}
      </div>

      {% if fixed_amount and fixed_amount > 0 %}
        <div class="rec" style="background:#ecfdf5;border-left-color:#10b981;">
          Amount due: <b>KES {{ "%.2f"|format(fixed_amount) }}</b>
          ({{ "%.2f"|format(fixed_amount / psc_rate) }} PSC)
        </div>
        <input type="hidden" id="amount" value="{{ '%.2f'|format(fixed_amount) }}">
      {% else %}
        <label for="amount">Amount (KES)</label>
        <input type="number" id="amount" min="{{ min_kes }}"
               {% if max_kes > 0 %}max="{{ max_kes }}"{% endif %}
               placeholder="e.g. 500" required>
        <div class="amount-note">Minimum KES {{ "%.2f"|format(min_kes) }}{% if max_kes > 0 %} &middot; maximum KES {{ "%.2f"|format(max_kes) }}{% endif %}</div>
      {% endif %}

      <label for="name">Your name (optional)</label>
      <input type="text" id="name" placeholder="Jane Doe">

      <label for="email">Email (for receipt)</label>
      <input type="email" id="email" placeholder="you@example.com" required>

      <label for="phone">Phone (optional)</label>
      <input type="text" id="phone" placeholder="07XXXXXXXX">

      <button class="btn" id="payBtn">Pay with {{ gateway|capitalize }}</button>
      <div class="msg" id="msg"></div>
    {% endif %}
    <div class="powered">Secured by <b>PSC - Pulse Shopping Coin</b></div>
  </div>

<script>
(function(){
  var TOKEN = {{ token|tojson }};
  var GATEWAY = {{ gateway|tojson }};

  // === ADDITIVE: auto-verify on return from Flutterwave ===
  try {
    var _qs = new URLSearchParams(window.location.search);
    var _txr = _qs.get('tx_ref');
    if (_txr) {
      var _box = document.getElementById('msg');
      if (_box) { _box.className = 'msg ok'; _box.textContent = 'Verifying your payment...'; }
      fetch('/api/payment_link/verify', {
        method: 'POST', headers: {'Content-Type':'application/json'},
        body: JSON.stringify({ token: TOKEN, tx_ref: _txr })
      })
      .then(function(r){ return r.json(); })
      .then(function(d){
        var el = document.getElementById('msg'); if (!el) return;
        if (d && d.success) { el.className = 'msg ok';
          el.textContent = d.message || 'Payment confirmed. Awaiting admin approval.'; }
        else { el.className = 'msg err';
          el.textContent = (d && d.message) || 'Could not verify payment.'; }
      })
      .catch(function(e){ var el = document.getElementById('msg');
        if (el) { el.className = 'msg err'; el.textContent = 'Verify error: ' + e; } });
    }
  } catch (e) { /* ignore */ }
  // === END ADDITIVE ===

  var btn = document.getElementById('payBtn');
  if (!btn) return;

  function show(msg, isErr){
    var el = document.getElementById('msg');
    el.textContent = msg;
    el.className = 'msg ' + (isErr ? 'err' : 'ok');
  }

  btn.addEventListener('click', function(){
    var amountEl = document.getElementById('amount');
    var amount = amountEl ? parseFloat(amountEl.value || '0') : 0;
    var email = (document.getElementById('email').value || '').trim();
    var name  = (document.getElementById('name').value || '').trim();
    var phone = (document.getElementById('phone').value || '').trim();

    if (!amount || amount <= 0) { show('Enter a valid amount.', true); return; }
    if (!email) { show('Email is required for your receipt.', true); return; }

    btn.disabled = true;
    show('Creating secure checkout...', false);

    fetch('/api/payment_link/' + encodeURIComponent(TOKEN) + '/initiate', {
      method: 'POST',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({
        amount_kes: amount,
        payer_name: name,
        payer_email: email,
        payer_phone: phone
      })
    })
    .then(function(r){ return r.json(); })
    .then(function(d){
      if (!d || !d.success) {
        show((d && d.message) || 'Could not start payment.', true);
        btn.disabled = false;
        return;
      }
      show('Redirecting to secure checkout...', false);
      window.location.href = d.checkout_url;
    })
    .catch(function(e){
      show('Network error: ' + e, true);
      btn.disabled = false;
    });
  });
})();
</script>
</body>
</html>
"""
# ============================================================
# END PAYMENT LINKS
# ============================================================


# ============================================================
# COINGATE GATEWAY - ADDITIVE, OFF BY DEFAULT
# Supports BTC, ETH, USDT-TRC20.
# ============================================================

COINGATE_ENABLED     = os.getenv("COINGATE_ENABLED", "0").strip() == "1"
COINGATE_API_TOKEN   = os.getenv("COINGATE_API_TOKEN", "")
COINGATE_MODE        = os.getenv("COINGATE_MODE", "sandbox").strip().lower()
COINGATE_BASE_URL    = ("https://api-sandbox.coingate.com/v2"
                        if COINGATE_MODE == "sandbox"
                        else "https://api.coingate.com/v2")
COINGATE_ALLOWED_CURRENCIES = [
    c.strip().upper()
    for c in os.getenv("COINGATE_ALLOWED_CURRENCIES", "BTC,ETH,USDT").split(",")
    if c.strip()
]
COINGATE_DEFAULT_RECEIVE = os.getenv("COINGATE_RECEIVE_CUR", "USDT").strip().upper()
COINGATE_SETTLE_CUR      = os.getenv("COINGATE_SETTLE_CUR",  "EUR").strip().upper()
COINGATE_KES_PER_USD     = float(os.getenv("COINGATE_KES_PER_USD", "0") or 0)
COINGATE_MIN_KES         = float(os.getenv("COINGATE_MIN_KES", "100") or 100)
COINGATE_MAX_KES         = float(os.getenv("COINGATE_MAX_KES", "0") or 0)

COINGATE_PAYMENTS_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "coingate_payments.json"
)


def _cg_headers():
    return {
        "Authorization": f"Token {COINGATE_API_TOKEN}",
        "Content-Type":  "application/json",
        "Accept":        "application/json",
    }


def _cg_payments_all():
    d = _jload(COINGATE_PAYMENTS_FILE, [])
    return d if isinstance(d, list) else []


def _cg_payment_find(order_id):
    for row in _cg_payments_all():
        if row.get("order_id") == order_id:
            return row
    return None


def _cg_payment_add(row):
    rows = _cg_payments_all()
    rows.append(row)
    _jsave(COINGATE_PAYMENTS_FILE, rows)


def _cg_payment_update(order_id, **fields):
    rows = _cg_payments_all()
    for r in rows:
        if r.get("order_id") == order_id:
            r.update(fields)
            _jsave(COINGATE_PAYMENTS_FILE, rows)
            return r
    return None


def _cg_normalize_receive_currency(raw):
    if not raw:
        raw = COINGATE_DEFAULT_RECEIVE
    s = str(raw).strip().upper().replace("-", "").replace("_", "").replace(" ", "")
    if s in ("USDTTRC20", "TRC20USDT", "USDTTRON", "TRONUSDT", "USDT"):
        if "USDT" in COINGATE_ALLOWED_CURRENCIES:
            return "USDT", "TRC20"
        return None, "USDT is not in COINGATE_ALLOWED_CURRENCIES"
    if s in COINGATE_ALLOWED_CURRENCIES:
        return s, ""
    return None, f"Currency '{raw}' not in allowlist {COINGATE_ALLOWED_CURRENCIES}"


def _cg_kes_to_settle(amount_kes):
    if COINGATE_KES_PER_USD > 0 and COINGATE_SETTLE_CUR in ("USD", "USDT", "USDC", "EUR"):
        amt = round(amount_kes / COINGATE_KES_PER_USD, 2)
        return amt, COINGATE_KES_PER_USD
    return round(amount_kes, 2), 1.0


@app.route("/api/psc/topup/initiate_cg", methods=["POST"])
def api_psc_topup_initiate_cg():
    if not COINGATE_ENABLED:
        return jsonify({"success": False,
                        "message": "CoinGate is disabled (COINGATE_ENABLED=0)."}), 503
    if not COINGATE_API_TOKEN:
        return jsonify({"success": False,
                        "message": "CoinGate token not configured in .env"}), 500
    try:
        data = request.get_json() or {}
        user = session.get("user")
        session_wallet = session.get("wallet", "")
        if not user or not session_wallet:
            return jsonify({"success": False,
                            "message": "Please log in to buy PSC."}), 401

        address = str(data.get("wallet") or session_wallet or "").strip()
        if address != session_wallet:
            return jsonify({"success": False,
                            "message": "Wallet does not match the logged-in account."}), 403

        verified_phone = session.get("verified_phone", "")
        if not verified_phone:
            return jsonify({"success": False,
                            "message": "Verify your phone before buying PSC."}), 403

        client = get_client_by_phone(verified_phone)
        if not client or str(client.get("wallet_address", "")).strip() != address:
            return jsonify({"success": False,
                            "message": "Your verified phone does not belong to this wallet."}), 403

        amount_kes = float(data.get("amount_kes") or 0)
        if amount_kes < COINGATE_MIN_KES:
            return jsonify({"success": False,
                            "message": f"Minimum CoinGate top-up is KES {COINGATE_MIN_KES:.2f}."}), 400
        if COINGATE_MAX_KES > 0 and amount_kes > COINGATE_MAX_KES + 1e-9:
            return jsonify({"success": False,
                            "message": f"Maximum CoinGate top-up is KES {COINGATE_MAX_KES:.2f}."}), 400

        wallet = get_wallet(address)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"}), 404

        target = _normalize_credit_target(
            data.get("target") or data.get("credit_target") or "spendable"
        )

        receive_currency, net_hint = _cg_normalize_receive_currency(
            data.get("receive_currency") or data.get("token")
        )
        if not receive_currency:
            return jsonify({"success": False,
                            "message": net_hint,
                            "allowed_currencies": COINGATE_ALLOWED_CURRENCIES}), 400

        settle_amount, rate_used = _cg_kes_to_settle(amount_kes)
        expected_psc = round(amount_kes / PSC_TO_KES_RATE, 2)
        order_id = "PSC-CG-" + uuid.uuid4().hex[:16]

        _cg_payment_add({
            "order_id": order_id,
            "wallet_address": address,
            "amount_kes": round(amount_kes, 2),
            "settle_amount": settle_amount,
            "settle_currency": COINGATE_SETTLE_CUR,
            "receive_currency": receive_currency,
            "network_hint": net_hint,
            "rate_used": rate_used,
            "expected_psc": expected_psc,
            "status": "PENDING",
            "provider": "coingate",
            "cg_order_id": None,
            "created_at": _now(),
            "verified_at": None,
            "credited_psc": 0.0,
            "target": target,
        })

        redirect_url = (str(data.get("redirect_url") or "").strip()
                        or request.url_root.rstrip("/") + "/psc_topup_return")

        payload = {
            "order_id":          order_id,
            "price_amount":      settle_amount,
            "price_currency":    COINGATE_SETTLE_CUR,
            "receive_currency":  receive_currency,
            "title":             "PSC Top-Up",
            "description":       f"Buy {expected_psc} PSC for KES {amount_kes:.2f}",
            "callback_url":      request.url_root.rstrip("/") + "/webhooks/coingate",
            "cancel_url":        redirect_url,
            "success_url":       redirect_url,
            "token":             receive_currency,
        }

        r = _http.post(f"{COINGATE_BASE_URL}/orders",
                       json=payload, headers=_cg_headers(), timeout=20)
        resp = r.json() if r.content else {}

        print(f"[COINGATE] status={r.status_code} resp={str(resp)[:400]}")

        if r.status_code >= 300 or not resp.get("id"):
            _cg_payment_update(order_id, status="FAILED", error=str(resp)[:300])
            return jsonify({"success": False,
                            "message": str(resp.get("message") or "CoinGate error")}), 502

        _cg_payment_update(order_id, cg_order_id=resp.get("id"))

        return jsonify({
            "success": True,
            "order_id": order_id,
            "checkout_url": resp.get("payment_url"),
            "amount_kes": round(amount_kes, 2),
            "settle_amount": settle_amount,
            "settle_currency": COINGATE_SETTLE_CUR,
            "receive_currency": receive_currency,
            "network_hint": net_hint,
            "expected_psc": expected_psc,
            "gateway": "coingate",
            "target": target,
            "allowed_currencies": COINGATE_ALLOWED_CURRENCIES,
            "message": "Open the checkout link to pay with crypto.",
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


def _cg_verify_and_credit(order_id, cg_order_id=None):
    row = _cg_payment_find(order_id)
    if not row:
        return False, "Unknown order_id", None
    if row.get("status") == "COMPLETED":
        return True, "Already credited", row
    if row.get("status") == "FAILED":
        return False, "Order previously FAILED", row
    if not COINGATE_API_TOKEN:
        return False, "CoinGate token not configured", row

    cg_id = cg_order_id or row.get("cg_order_id")
    if not cg_id:
        return False, "CoinGate order id missing", row

    try:
        r = _http.get(f"{COINGATE_BASE_URL}/orders/{cg_id}",
                      headers=_cg_headers(), timeout=20)
        resp = r.json() if r.content else {}
        if r.status_code >= 300 or not resp.get("id"):
            return False, resp.get("message") or "Verify failed", row

        status = str(resp.get("status") or "").lower()
        if status not in ("paid", "confirmed", "complete"):
            _cg_payment_update(order_id, status="PENDING", cg_status=status)
            return False, f"CoinGate status: {status}", row

        psc_amount = float(row["expected_psc"])
        kes_amount = float(row["amount_kes"])
        target = _normalize_credit_target(row.get("target") or "spendable")

        ok, msg, _wallet = _add_psc_to_target(
            row["wallet_address"], psc_amount,
            target=target, kes_amount=kes_amount,
            payment_reference=f"CG:{order_id}",
            audit_type="COINGATE_TOPUP",
        )
        if not ok:
            _cg_payment_update(order_id, status="FAILED",
                               error=f"credit failed: {msg}")
            return False, f"Credit failed: {msg}", row

        _cg_payment_update(order_id, status="COMPLETED",
                           cg_status=status,
                           verified_at=_now(),
                           credited_psc=psc_amount, error="")
        _close_partial_if_any(row["wallet_address"])

        try:
            if kes_amount >= CBK_REPORT_THRESHOLD_KES:
                _compliance_flag_add({
                    "at": _now(), "wallet": row["wallet_address"],
                    "type": "LARGE_CRYPTO_INFLOW",
                    "amount_kes": kes_amount, "order_id": order_id,
                })
        except Exception as _cg_cbk_e:
            print(f"[COINGATE] CBK flag skipped: {_cg_cbk_e}")

        return True, f"Credited {psc_amount:.2f} PSC", _cg_payment_find(order_id)
    except Exception as e:
        return False, str(e), row


@app.route("/api/psc/topup/verify_cg", methods=["POST"])
def api_psc_topup_verify_cg():
    try:
        data = request.get_json() or {}
        order_id = str(data.get("order_id") or data.get("tx_ref") or "").strip()
        if not order_id:
            return jsonify({"success": False, "message": "order_id required"}), 400
        ok, msg, row = _cg_verify_and_credit(
            order_id, cg_order_id=data.get("cg_order_id")
        )
        return jsonify({"success": ok, "message": msg,
                        "payment": row, "gateway": "coingate"}), (200 if ok else 400)
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/psc/topup/status_cg/<order_id>")
def api_psc_topup_status_cg(order_id):
    row = _cg_payment_find(order_id)
    if not row:
        return jsonify({"success": False, "message": "not found"}), 404
    return jsonify({"success": True, "payment": row, "gateway": "coingate"})


@app.route("/api/psc/topup/history_cg/<address>")
def api_psc_topup_history_cg(address):
    rows = [r for r in _cg_payments_all() if r.get("wallet_address") == address]
    return jsonify({"success": True, "payments": rows, "gateway": "coingate"})


@app.route("/api/psc/topup/currencies_cg", methods=["GET"])
def api_psc_topup_currencies_cg():
    currencies = []
    for c in COINGATE_ALLOWED_CURRENCIES:
        if c == "USDT":
            currencies.append({
                "key": "USDT", "label": "USDT (TRC20)",
                "network": "TRC20",
                "aliases": ["USDT-TRC20", "USDT_TRC20", "USDTTRC20", "TRC20-USDT"],
            })
        elif c == "BTC":
            currencies.append({"key": "BTC", "label": "Bitcoin", "network": "Bitcoin"})
        elif c == "ETH":
            currencies.append({"key": "ETH", "label": "Ethereum", "network": "ERC20"})
        else:
            currencies.append({"key": c, "label": c, "network": ""})
    return jsonify({
        "success": True,
        "enabled": COINGATE_ENABLED and bool(COINGATE_API_TOKEN),
        "default": COINGATE_DEFAULT_RECEIVE,
        "settle_currency": COINGATE_SETTLE_CUR,
        "min_kes": COINGATE_MIN_KES,
        "max_kes": COINGATE_MAX_KES,
        "currencies": currencies,
    })


@app.route("/webhooks/coingate", methods=["POST"])
def webhook_coingate():
    try:
        raw = request.get_data() or b""
        body = json.loads(raw.decode("utf-8") or "{}")
        cg_id = str(body.get("id") or "").strip()
        order_id = str(body.get("order_id") or "").strip()
        if not order_id and cg_id:
            for r in _cg_payments_all():
                if str(r.get("cg_order_id")) == cg_id:
                    order_id = r.get("order_id")
                    break
        if not order_id:
            return jsonify({"success": True, "message": "ignored"}), 200
        _cg_verify_and_credit(order_id, cg_order_id=cg_id or None)
        return jsonify({"success": True}), 200
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# END COINGATE GATEWAY
# ============================================================


# ============================================================
# MOONPAY GATEWAY - ADDITIVE, OFF BY DEFAULT
# Crypto on-ramp via card. BTC, ETH, USDT-TRC20, USDC.
# ============================================================

MOONPAY_ENABLED          = os.getenv("MOONPAY_ENABLED", "0").strip() == "1"
MOONPAY_PUBLISHABLE_KEY  = os.getenv("MOONPAY_PUBLISHABLE_KEY", "")
MOONPAY_SECRET_KEY       = os.getenv("MOONPAY_SECRET_KEY", "")
MOONPAY_MODE             = os.getenv("MOONPAY_MODE", "sandbox").strip().lower()
MOONPAY_CURRENCY_CODE    = os.getenv("MOONPAY_CURRENCY_CODE", "kes").strip().lower()
MOONPAY_BASE_CURRENCY    = os.getenv("MOONPAY_BASE_CURRENCY", "usdt").strip().lower()
MOONPAY_ALLOWED_CRYPTOS  = [
    c.strip().lower()
    for c in os.getenv("MOONPAY_ALLOWED_CRYPTOS", "btc,eth,usdt,usdc").split(",")
    if c.strip()
]
MOONPAY_MIN_KES          = float(os.getenv("MOONPAY_MIN_KES", "500") or 500)
MOONPAY_MAX_KES          = float(os.getenv("MOONPAY_MAX_KES", "0") or 0)
MOONPAY_REDIRECT_URL     = os.getenv("MOONPAY_REDIRECT_URL", "").strip()
MOONPAY_WEBHOOK_SECRET   = os.getenv("MOONPAY_WEBHOOK_SECRET", "")

MOONPAY_PAYMENTS_FILE = os.path.join(
    os.path.dirname(PAYMENTS_FILE) or ".",
    "moonpay_payments.json"
)


def _mp_payments_all():
    d = _jload(MOONPAY_PAYMENTS_FILE, [])
    return d if isinstance(d, list) else []


def _mp_payment_find(tx_ref):
    for row in _mp_payments_all():
        if row.get("tx_ref") == tx_ref:
            return row
    return None


def _mp_payment_add(row):
    rows = _mp_payments_all()
    rows.append(row)
    _jsave(MOONPAY_PAYMENTS_FILE, rows)


def _mp_payment_update(tx_ref, **fields):
    rows = _mp_payments_all()
    for r in rows:
        if r.get("tx_ref") == tx_ref:
            r.update(fields)
            _jsave(MOONPAY_PAYMENTS_FILE, rows)
            return r
    return None


def _mp_normalize_crypto(raw):
    if not raw:
        raw = MOONPAY_BASE_CURRENCY
    s = str(raw).strip().lower().replace("-", "").replace("_", "").replace(" ", "")
    if s in ("usdttrc20", "trc20usdt", "usdttron", "tronusdt", "usdt"):
        return ("usdt", "TRC20") if "usdt" in MOONPAY_ALLOWED_CRYPTOS else (None, "USDT not in allowlist")
    if s in MOONPAY_ALLOWED_CRYPTOS:
        return s, ""
    return None, f"Currency {raw} not in allowlist {MOONPAY_ALLOWED_CRYPTOS}"


def _mp_build_signature(url):
    if not MOONPAY_SECRET_KEY:
        return url
    try:
        from urllib.parse import urlparse, urlunparse
        import base64

        parsed = urlparse(url)
        query_with_q = "?" + parsed.query if parsed.query else ""
        if not query_with_q:
            return url

        sig = hmac.new(
            MOONPAY_SECRET_KEY.encode("utf-8"),
            query_with_q.encode("utf-8"),
            hashlib.sha256,
        ).digest()
        sig_b64 = base64.b64encode(sig).decode("utf-8")

        new_query = parsed.query + "&signature=" + sig_b64
        new_parsed = parsed._replace(query=new_query)
        return urlunparse(new_parsed)
    except Exception as e:
        print(f"[MOONPAY] signature build failed: {e}")
        return url


@app.route("/api/psc/topup/initiate_mp", methods=["POST"])
def api_psc_topup_initiate_mp():
    if not MOONPAY_ENABLED:
        return jsonify({"success": False,
                        "message": "MoonPay is disabled (MOONPAY_ENABLED=0)."}), 503
    if not MOONPAY_PUBLISHABLE_KEY:
        return jsonify({"success": False,
                        "message": "MoonPay publishable key not configured in .env"}), 500
    try:
        data = request.get_json() or {}
        user = session.get("user")
        session_wallet = session.get("wallet", "")
        if not user or not session_wallet:
            return jsonify({"success": False,
                            "message": "Please log in to buy PSC."}), 401

        address = str(data.get("wallet") or session_wallet or "").strip()
        if address != session_wallet:
            return jsonify({"success": False,
                            "message": "Wallet does not match the logged-in account."}), 403

        verified_phone = session.get("verified_phone", "")
        if not verified_phone:
            return jsonify({"success": False,
                            "message": "Verify your phone before buying PSC."}), 403

        client = get_client_by_phone(verified_phone)
        if not client or str(client.get("wallet_address", "")).strip() != address:
            return jsonify({"success": False,
                            "message": "Your verified phone does not belong to this wallet."}), 403

        amount_kes = float(data.get("amount_kes") or 0)
        if amount_kes < MOONPAY_MIN_KES:
            return jsonify({"success": False,
                            "message": f"Minimum MoonPay top-up is KES {MOONPAY_MIN_KES:.2f}."}), 400
        if MOONPAY_MAX_KES > 0 and amount_kes > MOONPAY_MAX_KES + 1e-9:
            return jsonify({"success": False,
                            "message": f"Maximum MoonPay top-up is KES {MOONPAY_MAX_KES:.2f}."}), 400

        wallet = get_wallet(address)
        if not wallet:
            return jsonify({"success": False, "message": "Wallet not found"}), 404

        target = _normalize_credit_target(
            data.get("target") or data.get("credit_target") or "spendable"
        )

        crypto_currency, net_hint = _mp_normalize_crypto(
            data.get("crypto_currency") or data.get("cryptocurrency")
        )
        if not crypto_currency:
            return jsonify({"success": False,
                            "message": net_hint,
                            "allowed_cryptos": MOONPAY_ALLOWED_CRYPTOS}), 400

        expected_psc = round(amount_kes / PSC_TO_KES_RATE, 2)
        tx_ref = "PSC-MP-" + uuid.uuid4().hex[:16]

        _mp_payment_add({
            "tx_ref": tx_ref,
            "wallet_address": address,
            "amount_kes": round(amount_kes, 2),
            "crypto_currency": crypto_currency,
            "network_hint": net_hint,
            "expected_psc": expected_psc,
            "status": "PENDING",
            "provider": "moonpay",
            "target": target,
            "created_at": _now(),
            "verified_at": None,
            "credited_psc": 0.0,
            "mode": MOONPAY_MODE,
        })

        email = client.get("email") or "customer@example.com"
        redirect_url = (MOONPAY_REDIRECT_URL
                        or (request.url_root.rstrip("/") + "/psc_topup_return?tx_ref=" + tx_ref))

        buy_url = (
            "https://buy.moonpay.com"
            "?apiKey=" + MOONPAY_PUBLISHABLE_KEY +
            "&currencyCode=" + crypto_currency +
            "&baseCurrencyCode=" + MOONPAY_CURRENCY_CODE +
            "&baseCurrencyAmount=" + str(round(amount_kes, 2)) +
            "&email=" + email +
            "&externalTransactionId=" + tx_ref +
            "&redirectURL=" + redirect_url +
            "&walletAddress=" + address +
            "&lockAmount=true"
        )

        signed_url = _mp_build_signature(buy_url)

        print(f"[MOONPAY] initiate tx_ref={tx_ref} crypto={crypto_currency} amount_kes={amount_kes}")

        return jsonify({
            "success": True,
            "tx_ref": tx_ref,
            "checkout_url": signed_url,
            "amount_kes": round(amount_kes, 2),
            "crypto_currency": crypto_currency,
            "network_hint": net_hint,
            "expected_psc": expected_psc,
            "target": target,
            "gateway": "moonpay",
            "allowed_cryptos": MOONPAY_ALLOWED_CRYPTOS,
            "mode": MOONPAY_MODE,
            "message": "Open the MoonPay checkout to complete payment by card.",
        })
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


def _mp_verify_and_credit(tx_ref, external_tx_id=None, crypto_amount=None):
    row = _mp_payment_find(tx_ref)
    if not row:
        return False, "Unknown tx_ref", None
    if row.get("status") == "COMPLETED":
        return True, "Already credited", row
    if row.get("status") == "FAILED":
        return False, "Payment previously FAILED", row

    try:
        psc_amount = float(row["expected_psc"])
        kes_amount = float(row["amount_kes"])
        target = _normalize_credit_target(row.get("target") or "spendable")

        ok, msg, _wallet = _add_psc_to_target(
            row["wallet_address"], psc_amount,
            target=target, kes_amount=kes_amount,
            payment_reference="MP:" + tx_ref,
            audit_type="MOONPAY_TOPUP",
        )
        if not ok:
            _mp_payment_update(tx_ref, status="FAILED",
                               error="credit failed: " + msg)
            return False, "Credit failed: " + msg, row

        _mp_payment_update(tx_ref, status="COMPLETED",
                           external_tx_id=external_tx_id,
                           crypto_amount=crypto_amount,
                           verified_at=_now(),
                           credited_psc=psc_amount, error="")
        _close_partial_if_any(row["wallet_address"])

        try:
            if kes_amount >= CBK_REPORT_THRESHOLD_KES:
                _compliance_flag_add({
                    "at": _now(), "wallet": row["wallet_address"],
                    "type": "LARGE_MOONPAY_INFLOW",
                    "amount_kes": kes_amount, "tx_ref": tx_ref,
                })
        except Exception as _mp_cbk_e:
            print(f"[MOONPAY] CBK flag skipped: {_mp_cbk_e}")

        return True, f"Credited {psc_amount:.2f} PSC", _mp_payment_find(tx_ref)
    except Exception as e:
        return False, str(e), row


@app.route("/api/psc/topup/verify_mp", methods=["POST"])
def api_psc_topup_verify_mp():
    try:
        data = request.get_json() or {}
        tx_ref = str(data.get("tx_ref") or "").strip()
        if not tx_ref:
            return jsonify({"success": False, "message": "tx_ref required"}), 400
        ok, msg, row = _mp_verify_and_credit(
            tx_ref,
            external_tx_id=data.get("external_tx_id"),
            crypto_amount=data.get("crypto_amount"),
        )
        return jsonify({"success": ok, "message": msg,
                        "payment": row, "gateway": "moonpay"}), (200 if ok else 400)
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


@app.route("/api/psc/topup/status_mp/<tx_ref>")
def api_psc_topup_status_mp(tx_ref):
    row = _mp_payment_find(tx_ref)
    if not row:
        return jsonify({"success": False, "message": "not found"}), 404
    return jsonify({"success": True, "payment": row, "gateway": "moonpay"})


@app.route("/api/psc/topup/history_mp/<address>")
def api_psc_topup_history_mp(address):
    rows = [r for r in _mp_payments_all() if r.get("wallet_address") == address]
    return jsonify({"success": True, "payments": rows, "gateway": "moonpay"})


@app.route("/api/psc/topup/cryptos_mp", methods=["GET"])
def api_psc_topup_cryptos_mp():
    cryptos = []
    for c in MOONPAY_ALLOWED_CRYPTOS:
        if c == "usdt":
            cryptos.append({
                "key": "usdt", "label": "USDT (TRC20)",
                "network": "TRC20",
                "aliases": ["USDT-TRC20", "USDT_TRC20", "USDTTRC20", "TRC20-USDT"],
            })
        elif c == "usdc":
            cryptos.append({"key": "usdc", "label": "USDC", "network": "ERC20"})
        elif c == "btc":
            cryptos.append({"key": "btc", "label": "Bitcoin", "network": "Bitcoin"})
        elif c == "eth":
            cryptos.append({"key": "eth", "label": "Ethereum", "network": "ERC20"})
        else:
            cryptos.append({"key": c, "label": c.upper(), "network": ""})

    return jsonify({
        "success": True,
        "enabled": MOONPAY_ENABLED and bool(MOONPAY_PUBLISHABLE_KEY),
        "mode": MOONPAY_MODE,
        "fiat_currency": MOONPAY_CURRENCY_CODE.upper(),
        "base_crypto": MOONPAY_BASE_CURRENCY,
        "min_kes": MOONPAY_MIN_KES,
        "max_kes": MOONPAY_MAX_KES,
        "cryptos": cryptos,
    })


@app.route("/webhooks/moonpay", methods=["POST"])
def webhook_moonpay():
    try:
        raw = request.get_data() or b""
        sent_sig = request.headers.get("Moonpay-Signature-V2", "") or request.headers.get("moonpay-signature-v2", "")

        if MOONPAY_WEBHOOK_SECRET:
            expected_sig = hmac.new(
                MOONPAY_WEBHOOK_SECRET.encode("utf-8"),
                raw,
                hashlib.sha256,
            ).hexdigest()
            if not sent_sig or not hmac.compare_digest(sent_sig.lower(), expected_sig.lower()):
                return jsonify({"success": False, "message": "bad signature"}), 401

        body = json.loads(raw.decode("utf-8") or "{}")
        event_type = str(body.get("type") or "").strip().lower()
        d = body.get("data") or {}

        if event_type in ("transaction_updated", "transaction.created",
                          "transaction.completed", "transaction_updated.completed"):
            status = str(d.get("status") or "").strip().lower()
            tx_ref = str(d.get("externalTransactionId") or "").strip()
            external_tx_id = str(d.get("id") or "").strip()
            crypto_amount = d.get("cryptoAmount")

            if not tx_ref:
                return jsonify({"success": True, "message": "ignored no tx_ref"}), 200

            if status not in ("completed", "succeeded"):
                _mp_payment_update(tx_ref, mp_status=status)
                return jsonify({"success": True, "message": "status=" + status}), 200

            _mp_verify_and_credit(tx_ref, external_tx_id, crypto_amount)
            return jsonify({"success": True}), 200

        return jsonify({"success": True, "message": "ignored event"}), 200
    except Exception as e:
        return jsonify({"success": False, "message": str(e)}), 500


# ============================================================
# END MOONPAY GATEWAY
# ============================================================

# ---------- CACHE WARMER ----------

# === PRIORITY_WARM_FIX ===
# Warmer order changed: popular keywords first so browser searches
# hit cached results quickly. Non-priority categories warm after.
def _warm_cache():
    # Delay warmer start so the shop is responsive on cold boot.
    time.sleep(60)
    while True:
        try:
            print(f"[PSC] Warming cache (priority keywords first)...")

            PRIORITY_KEYWORDS = [
                "smartphone", "smart tv", "home appliance", "beauty products",
                "laptop", "fashion", "home kitchen", "gaming console",
            ]

            for kw in PRIORITY_KEYWORDS:
                # Pause while users are active so their requests get
                # the scrape lock first instead of falling back.
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
                # === FIX 8: small jitter so the warmer does not monopolise
                # _SCRAPE_LOCK while real users are browsing. ===
                time.sleep(_jitter(1500, 2500) / 1000.0)
                # === END FIX 8 ===

            # Non-priority categories now warm lazily when a user
            # visits them. The warmer only cycles the 8 priority
            # keywords so it releases _SCRAPE_LOCK quickly.

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
# === END PRIORITY_WARM_FIX ===

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


# ---------- BACKGROUND THREADS ----------

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
            threading.Thread(target=_warm_cache, daemon=True).start()
            # === FIX #C ===
            # Named the midnight-bonus thread so any future hardened/debug
            # wrapper can detect that the original is already running and
            # will not spawn a duplicate. Behaviour is otherwise unchanged.
            threading.Thread(
                target=_midnight_bonus_loop,
                name="_midnight_bonus_loop",
                daemon=True
            ).start()
            print("[PSC] Background threads started (cache warmer + midnight bonus).")
        except Exception as e:
            print(f"[PSC] Failed to start background threads: {e}")


_start_background_threads_once()

# ============================================================
# ADDITIVE: BLOCKCHAIN MINING + REAL-TIME WEBSOCKET (SocketIO)
# Nothing above is modified. All logic below is purely additive.
#   /api/mine              -> mine a block with supplied txs
#   /api/mine_empty        -> mine an empty block
#   /api/blockchain        -> inspect chain (latest 10 by default)
#   /api/blockchain/validate -> verify chain integrity
#   SocketIO events        -> connected, subscribed, new_block,
#                             my_block, wallet_update, pong_psc
# ============================================================

# ----- SocketIO (optional; fail-open if package missing) -----
try:
    from flask_socketio import SocketIO, emit as ws_emit, join_room, leave_room
    _SOCKETIO_AVAILABLE = True
except Exception as _sio_imp_err:
    print(f"[PSC WS] flask_socketio not installed ({_sio_imp_err}). "
          f"WebSocket push disabled; mining endpoints still active.")
    _SOCKETIO_AVAILABLE = False


# ----- Blockchain config -----
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
    """
    Runs PoW while holding _BLOCKCHAIN_LOCK, then appends the block.
    Returns (block_dict, "OK") on success, (None, reason) on failure.
    """
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
    """Credit the configured mining reward into the miner's spendable PSC."""
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


# ---------------- Mining endpoints ----------------

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


# ---------------- SocketIO wiring ----------------

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

    # ---- Auto-broadcast wallet updates for ANY existing endpoint ----
    # This is how we get real-time push WITHOUT editing existing code.
    # Any successful JSON response from /api/wallet*, /api/account*,
    # /api/checkout*, or /api/place* that carries a wallet + balance
    # gets fanned out to that wallet's room.
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
            # We are being called from inside socketio.run() itself.
            # Hand off to the real Werkzeug server. Werkzeug's run_simple()
            # does not understand allow_unsafe_werkzeug � it's a
            # flask-socketio-only kwarg. Strip it before forwarding.
            kwargs.pop("allow_unsafe_werkzeug", None)
            return _original_app_run(*args, **kwargs)

        # Only the outer call (the one coming from __main__) reaches here.
        kwargs.setdefault("allow_unsafe_werkzeug", True)
        _psc_in_socketio_run = True
        try:
            return socketio.run(app, *args, **kwargs)
        finally:
            _psc_in_socketio_run = False

    app.run = _socketio_app_run

# ============================================================
# END ADDITIVE: BLOCKCHAIN MINING + REAL-TIME WEBSOCKET
# ============================================================


# ---------- START APPLICATION ----------

if __name__ == "__main__":
    print("=" * 60)
    print("  PSC - Pulse Shopping Coin (Client Site)")
    print("  Open: http://localhost:5001")
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
    print("  Vendor visibility: HIDDEN from client (source/vendor/vendor_url stripped)")
    print(f"  Disk cache: {DISK_CACHE_FILE}")
    print("  Daily VISIT bonus: ENABLED (idempotent per day, redeemable bucket)")
    print(f"  Virtual Accounts: {'ENABLED' if VA_ENABLED else 'DISABLED (VA_ENABLED=0)'}")
    print(f"  KYC required for VA: {'YES' if KYC_REQUIRED else 'NO'}")
    print(f"  Payout velocity: {PAYOUT_VELOCITY_MAX_PER_DAY}/day, {PAYOUT_VELOCITY_MAX_PER_WEEK}/week")
    print(f"  CBK report threshold: KES {CBK_REPORT_THRESHOLD_KES:,.2f}")
    print(f"  KRA WHT threshold:    KES {KRA_WHT_THRESHOLD_KES:,.2f}")
    print(f"  Payment gateways:     Flutterwave={'ON' if FLW_SECRET_KEY else 'OFF'} | "
          f"Paystack={'ON' if (PAYSTACK_ENABLED and PAYSTACK_SECRET_KEY) else 'OFF'}")
    print(f"  Wallet deposits:      deposit_max={'UNLIMITED' if WALLET_DEPOSIT_MAX_KES == 0 else f'KES {WALLET_DEPOSIT_MAX_KES:.2f}'} | "
          f"withdraw_daily_max=KES {WALLET_WITHDRAW_DAILY_MAX_KES:.2f} | "
          f"p2p=ENABLED")
    print(f"  Savings bucket:       {'ENABLED' if WALLET_SAVINGS_ENABLED else 'DISABLED'}")
    print(f"  Deposit PSC pocket:   {'ENABLED (hold-only)' if WALLET_DEPOSIT_POCKET_ENABLED else 'DISABLED'}")
    print(f"  Wallet UI manifest:   /api/wallet/ui/<wallet>")
    print(f"  Three-bucket credits: target='spendable' | 'savings' | 'deposit'")
    print("  Fallback products:    ENABLED (no empty grids when scraping fails)")
    print("=" * 60)

    app.run(
        debug=False,
        host="0.0.0.0",
        port=5001,
        threaded=True,
        use_reloader=False
    )


