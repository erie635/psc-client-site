"""
auto_share.py - PSC Auto-Shareable Links
Makes /pay/<token> URLs work on ANY device automatically while the
app runs on localhost and the PC is online.
"""
import atexit
import os
import re
import shutil
import subprocess
import threading
import time
from datetime import datetime

_LOCK = threading.Lock()
_STATE = {
    "enabled": True,
    "running": False,
    "public_url": "",
    "tunnel_proc": None,
    "started_at": None,
    "restarts": 0,
    "last_error": "",
    "cloudflared_path": "",
    "log_tail": [],
}
_LOG_TAIL_MAX = 40


def _now():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def _log(line):
    try:
        with _LOCK:
            _STATE["log_tail"].append(f"[{_now()}] {line}")
            if len(_STATE["log_tail"]) > _LOG_TAIL_MAX:
                _STATE["log_tail"] = _STATE["log_tail"][-_LOG_TAIL_MAX:]
    except Exception:
        pass


def _find_cloudflared():
    p = shutil.which("cloudflared")
    if p:
        return p
    for c in [
        os.path.expanduser(r"~\cloudflared.exe"),
        r"C:\Program Files (x86)\cloudflared\cloudflared.exe",
        r"C:\Program Files\cloudflared\cloudflared.exe",
        r"C:\ProgramData\chocolatey\bin\cloudflared.exe",
    ]:
        if os.path.exists(c):
            return c
    return ""


def _parse_tunnel_url(line):
    m = re.search(r"https://[a-zA-Z0-9\-]+\.trycloudflare\.com", line or "")
    return m.group(0) if m else ""


def _reader_thread(proc, port):
    try:
        for raw in iter(proc.stderr.readline, b""):
            try:
                line = raw.decode("utf-8", errors="replace").rstrip()
            except Exception:
                continue
            if not line:
                continue
            _log(line)
            if not _STATE["public_url"]:
                url = _parse_tunnel_url(line)
                if url:
                    with _LOCK:
                        _STATE["public_url"] = url
                        os.environ["PSC_PUBLIC_BASE_URL"] = url
                    _log(f"PUBLIC URL detected: {url}")
    except Exception as e:
        _log(f"reader stopped: {e}")
    finally:
        with _LOCK:
            _STATE["running"] = False


def _start_tunnel(port=5001):
    cf = _find_cloudflared()
    if not cf:
        _log("cloudflared not found.")
        with _LOCK:
            _STATE["last_error"] = "cloudflared not installed"
        return False
    with _LOCK:
        _STATE["cloudflared_path"] = cf
    args = [cf, "tunnel", "--url", f"http://localhost:{port}", "--no-autoupdate"]
    _log("Starting: " + " ".join(args))
    try:
        proc = subprocess.Popen(
            args,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            bufsize=1,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
        )
    except Exception as e:
        _log(f"spawn failed: {e}")
        with _LOCK:
            _STATE["last_error"] = str(e)
        return False
    with _LOCK:
        _STATE["tunnel_proc"] = proc
        _STATE["running"] = True
        _STATE["started_at"] = _now()
        _STATE["last_error"] = ""
    threading.Thread(target=_reader_thread, args=(proc, port), daemon=True).start()
    for _ in range(60):
        if _STATE["public_url"]:
            return True
        time.sleep(0.5)
    _log("Timed out waiting for public URL (30s).")
    with _LOCK:
        _STATE["last_error"] = "tunnel URL not detected in 30s"
    return False


def _stop_tunnel():
    with _LOCK:
        proc = _STATE.get("tunnel_proc")
    if proc:
        try:
            proc.terminate()
            try:
                proc.wait(timeout=5)
            except Exception:
                proc.kill()
        except Exception:
            pass
    with _LOCK:
        _STATE["tunnel_proc"] = None
        _STATE["running"] = False


def _supervisor_loop(port=5001):
    while True:
        time.sleep(8)
        if not _STATE["enabled"]:
            continue
        proc = _STATE.get("tunnel_proc")
        dead = (proc is None) or (proc.poll() is not None)
        if dead and _STATE["enabled"]:
            _log("Tunnel dead - restarting.")
            with _LOCK:
                _STATE["restarts"] += 1
                _STATE["public_url"] = ""
            _start_tunnel(port)


def public_base(fallback=""):
    with _LOCK:
        url = _STATE.get("public_url") or ""
    if url:
        return url.rstrip("/")
    env = os.getenv("PSC_PUBLIC_BASE_URL", "").strip().rstrip("/")
    if env:
        return env
    return (fallback or "").rstrip("/")


def is_shareable():
    with _LOCK:
        return bool(_STATE.get("public_url"))


def status():
    with _LOCK:
        return {
            "enabled": _STATE["enabled"],
            "running": _STATE["running"],
            "shareable": bool(_STATE["public_url"]),
            "public_url": _STATE["public_url"],
            "started_at": _STATE["started_at"],
            "restarts": _STATE["restarts"],
            "last_error": _STATE["last_error"],
            "cloudflared_path": _STATE["cloudflared_path"],
            "log_tail": list(_STATE["log_tail"]),
        }


def install(app, port=5001, auto_start=True):
    from flask import jsonify

    @app.route("/api/share/status", methods=["GET"])
    def _psc_share_status():
        return jsonify({"success": True, **status()})

    @app.route("/api/share/start", methods=["POST", "GET"])
    def _psc_share_start():
        with _LOCK:
            _STATE["enabled"] = True
        if is_shareable():
            return jsonify({"success": True, "message": "Already shareable", **status()})
        ok = _start_tunnel(port)
        return jsonify({"success": ok,
                        "message": "Tunnel started" if ok else "Tunnel failed",
                        **status()})

    @app.route("/api/share/stop", methods=["POST", "GET"])
    def _psc_share_stop():
        with _LOCK:
            _STATE["enabled"] = False
            _STATE["public_url"] = ""
            os.environ.pop("PSC_PUBLIC_BASE_URL", None)
        _stop_tunnel()
        return jsonify({"success": True, "message": "Auto-share disabled", **status()})

    @app.route("/api/share/restart", methods=["POST", "GET"])
    def _psc_share_restart():
        _stop_tunnel()
        with _LOCK:
            _STATE["enabled"] = True
            _STATE["public_url"] = ""
            _STATE["restarts"] += 1
        ok = _start_tunnel(port)
        return jsonify({"success": ok,
                        "message": "Tunnel restarted" if ok else "Restart failed",
                        **status()})

    @app.route("/api/share/links", methods=["GET"])
    def _psc_share_links():
        try:
            base = public_base()
            return jsonify({
                "success": True,
                "base_url": base,
                "shareable": is_shareable(),
                "hint": "See /api/payment_link/list/<wallet> for links.",
            })
        except Exception as e:
            return jsonify({"success": False, "message": str(e)}), 500

    atexit.register(_stop_tunnel)

    if auto_start and _STATE["enabled"]:
        def _delayed_start():
            time.sleep(2)
            _start_tunnel(port)
            threading.Thread(target=_supervisor_loop, args=(port,), daemon=True).start()
        threading.Thread(target=_delayed_start, daemon=True).start()

    _log("auto_share installed.")
    return True