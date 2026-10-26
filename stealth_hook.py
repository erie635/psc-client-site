"""PSC anti-block hook.
Monkey-patches Playwright so EVERY browser launch:
  - routes through PSC_PROXY_SERVER / PSC_PROXY_SERVERS (if set)
  - rotates a realistic desktop User-Agent
  - removes the automation flag and injects stealth JS
Nothing inside client_app.py is changed.
"""
import os, random

try:
    from playwright.sync_api import _generated
except Exception as e:
    print(f"[PSC-STEALTH] Playwright not importable: {e}")
    _generated = None

_PROXY_SERVER = os.getenv("PSC_PROXY_SERVER", "").strip()
_PROXY_USER   = os.getenv("PSC_PROXY_USERNAME", "").strip()
_PROXY_PASS   = os.getenv("PSC_PROXY_PASSWORD", "").strip()
_PROXY_LIST   = [s.strip() for s in os.getenv("PSC_PROXY_SERVERS", "").split(",") if s.strip()]

_USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:125.0) Gecko/20100101 Firefox/125.0",
]

_STEALTH_JS = r"""
Object.defineProperty(navigator, 'webdriver', { get: () => undefined });
Object.defineProperty(navigator, 'languages', { get: () => ['en-KE','en-US','en'] });
try {
  Object.defineProperty(navigator, 'plugins', { get: () => [
    {name: 'PDF Viewer'}, {name: 'Chrome PDF Viewer'}, {name: 'Native Client'}
  ]});
} catch (e) {}
window.chrome = window.chrome || { runtime: {}, app: {}, csi: function(){}, loadTimes: function(){} };
try {
  const _o = window.navigator.permissions.query;
  window.navigator.permissions.query = (p) => (
    p && p.name === 'notifications'
      ? Promise.resolve({ state: Notification.permission })
      : _o(p)
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


def _proxy_cfg():
    server = random.choice(_PROXY_LIST) if _PROXY_LIST else _PROXY_SERVER
    if not server:
        return None
    cfg = {"server": server}
    if _PROXY_USER: cfg["username"] = _PROXY_USER
    if _PROXY_PASS: cfg["password"] = _PROXY_PASS
    return cfg


if _generated is not None:
    _orig_launch = _generated.BrowserType.launch

    def _patched_launch(self, **kwargs):
        px = _proxy_cfg()
        if px and not kwargs.get("proxy"):
            kwargs["proxy"] = px
        args = list(kwargs.get("args") or [])
        for a in ("--disable-blink-features=AutomationControlled",
                  "--no-sandbox", "--disable-dev-shm-usage",
                  "--disable-gpu", "--window-size=1920,1080"):
            if a not in args:
                args.append(a)
        kwargs["args"] = args
        kwargs.setdefault("headless", True)
        return _orig_launch(self, **kwargs)

    _generated.BrowserType.launch = _patched_launch

    _orig_new_context = _generated.Browser.new_context

    def _patched_new_context(self, **kwargs):
        if not kwargs.get("user_agent"):
            kwargs["user_agent"] = random.choice(_USER_AGENTS)
        kwargs.setdefault("viewport", {"width": 1920, "height": 1080})
        kwargs.setdefault("locale", "en-KE")
        kwargs.setdefault("timezone_id", "Africa/Nairobi")
        kwargs.setdefault("extra_http_headers",
                          {"Accept-Language": "en-KE,en-US;q=0.9,en;q=0.8"})
        ctx = _orig_new_context(self, **kwargs)
        try:
            ctx.add_init_script(_STEALTH_JS)
        except Exception:
            pass
        return ctx

    _generated.Browser.new_context = _patched_new_context

    _orig_new_page = _generated.Browser.new_page

    def _patched_new_page(self, **kwargs):
        if not kwargs.get("user_agent"):
            kwargs["user_agent"] = random.choice(_USER_AGENTS)
        kwargs.setdefault("viewport", {"width": 1920, "height": 1080})
        kwargs.setdefault("locale", "en-KE")
        kwargs.setdefault("timezone_id", "Africa/Nairobi")
        return _orig_new_page(self, **kwargs)

    _generated.Browser.new_page = _patched_new_page

    _status = "ON" if (_PROXY_SERVER or _PROXY_LIST) else "OFF (set PSC_PROXY_SERVER in .env)"
    print(f"[PSC-STEALTH] Playwright patched | proxy={_status} | UA rotation=ON | stealth=ON")

# ---------- requests-path proxy (added) ----------
# Routes requests.get/post to KNOWN scrape hosts through the same proxy
# used by Playwright. Flutterwave / Paystack / CoinGate / MoonPay are
# deliberately NOT proxied, so their geolocation checks stay happy.
import requests as _rq_mod

_SCRAPE_HOSTS = (
    "jumia.co.ke", "kilimall.co.ke", "carrefour.ke", "jiji.co.ke",
    "fahavicomputers.co.ke", "textbookcentre.com", "naivas.co.ke",
    "vivo.co.ke", "copell.co.ke", "masoko.co.ke", "hotpoint.co.ke",
    "samsungbrandstore.co.ke",
)

_orig_rq_request = _rq_mod.api.request

def _rq_request_with_proxy(method, url, **kwargs):
    px = _proxy_cfg()
    if px and not kwargs.get("proxies"):
        try:
            host = url.split("//", 1)[1].split("/", 1)[0].split(":", 1)[0].lower()
        except Exception:
            host = ""
        if host and any(h in host for h in _SCRAPE_HOSTS):
            proxy_url = px["server"]
            if px.get("username") and px.get("password"):
                scheme, _, rest = proxy_url.partition("://")
                if scheme and rest:
                    proxy_url = f"{scheme}://{px['username']}:{px['password']}@{rest}"
            kwargs["proxies"] = {"http": proxy_url, "https": proxy_url}
    return _orig_rq_request(method, url, **kwargs)

_rq_mod.api.request = _rq_request_with_proxy
print("[PSC-STEALTH] requests scrape-path patched (proxies scrape hosts only)")


# ---------- Jumia 403-defer hook (added) ----------
# Wraps client_app._scrape_jumia at runtime. When Jumia 403s (or returns
# empty 3x in a row), further calls return [] immediately so the sequential
# scraper falls straight through to Kilimall / Carrefour / the extras
# without waiting for a Playwright timeout. Also silences the repeated
# "[PSC SCRAPE] Jumia 403 ..." and "Jumia produced 0 products" console spam.
#
# No edits to client_app.py. Runs in a daemon thread that waits for
# __main__ to finish loading, then monkey-patches the function.

import sys as _jh_sys
import builtins as _jh_bi
import time as _jh_t
import threading as _jh_th


def _jh_install():
    # Wait up to 60s for client_app (running as __main__) to finish loading.
    deadline = _jh_t.time() + 60.0
    main = None
    while _jh_t.time() < deadline:
        main = _jh_sys.modules.get("__main__")
        if (main is not None
                and hasattr(main, "_scrape_jumia")
                and hasattr(main, "_JUMIA_REQUESTS_BLOCKED_UNTIL")
                and hasattr(main, "_scrape_vendors_sequential")):
            break
        _jh_t.sleep(0.15)
    else:
        _jh_bi.print("[PSC-STEALTH] Jumia defer hook: __main__ not ready, skipped")
        return

    _st = {
        "silent_until": 0.0,        # stop calling Jumia
        "consecutive_empty": 0,
        "notified": False,
    }

    _orig_print = _jh_bi.print

    def _filtered_print(*args, **kwargs):
        # Suppress ONLY the specific spam lines.
        if args:
            try:
                s = " ".join(str(a) for a in args)
            except Exception:
                s = ""
            if "Jumia 403; requests path disabled" in s:
                return
            if "Jumia produced 0 products" in s:
                return
        return _orig_print(*args, **kwargs)

    _jh_bi.print = _filtered_print

    _orig_scrape_jumia = main._scrape_jumia

    def _wrapped_scrape_jumia(q, headers=None):
        now = _jh_t.time()

        # Fast exit: we're in a cooldown window.
        if now < _st["silent_until"]:
            return []

        try:
            result = _orig_scrape_jumia(q, headers)
        except Exception:
            result = []

        if result:
            _st["consecutive_empty"] = 0
            return result

        # Empty result. Count it.
        _st["consecutive_empty"] += 1
        new_blocked = float(getattr(main, "_JUMIA_REQUESTS_BLOCKED_UNTIL", 0.0) or 0.0)

        if new_blocked > now + 60:
            # App's own 403 flag was just set.
            _st["silent_until"] = new_blocked
            if not _st["notified"]:
                _orig_print(
                    "[PSC-STEALTH] Jumia 403 detected; deferring to "
                    "Kilimall/Carrefour until "
                    + _jh_t.strftime('%H:%M:%S', _jh_t.localtime(new_blocked))
                )
                _st["notified"] = True
        elif _st["consecutive_empty"] >= 3:
            # No 403 flag, but the scraper keeps returning nothing.
            # Cool down 15 min so the other vendors serve results.
            _st["silent_until"] = now + 900
            if not _st["notified"]:
                _orig_print(
                    "[PSC-STEALTH] Jumia returned 0 products 3x in a row; "
                    "cooling down 15 min, Kilimall/Carrefour will serve results"
                )
                _st["notified"] = True

        return result

    main._scrape_jumia = _wrapped_scrape_jumia

    # When the app's cooldown naturally expires, let Jumia try again.
    def _reset_loop():
        while True:
            _jh_t.sleep(30)
            try:
                if _st["silent_until"] and _jh_t.time() >= _st["silent_until"]:
                    _st["silent_until"] = 0.0
                    _st["consecutive_empty"] = 0
                    _st["notified"] = False
            except Exception:
                pass

    _jh_th.Thread(target=_reset_loop, daemon=True).start()
    _orig_print("[PSC-STEALTH] Jumia 403-defer hook installed "
                "(silences spam, falls through to Kilimall/Carrefour)")


_jh_th.Thread(target=_jh_install, daemon=True).start()
