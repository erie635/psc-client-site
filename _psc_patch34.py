# _psc_patch34.py -- applies P3 (endpoint fallback) + P4 (warmer covers all categories)
import io, shutil, time, ast, sys, os

os.chdir(r"C:\Users\erick\Desktop\PSC_Client_Site")
TARGET = "client_app.py"

with io.open(TARGET, "r", encoding="utf-8-sig") as f:
    src = f.read()
ENC = "utf-8"

orig = src
log = []

# ---------- P3: endpoint fallback ----------
old_block = (
    '            result[key] = {\n'
    '                "image": "",\n'
    '                "name":  "",\n'
    '                "emoji": cat.get("emoji", ""),\n'
    '            }\n'
)

new_block = (
    '            # -- FALLBACK 1: any product in memory with an image --\n'
    '            if not pick:\n'
    '                for _p in _PRODUCT_CACHE.values():\n'
    '                    if _p and _p.get("image"):\n'
    '                        pick = _p\n'
    '                        break\n'
    '\n'
    '            # -- FALLBACK 2: seller items --\n'
    '            if not pick:\n'
    '                try:\n'
    '                    for _it in _load_seller_items():\n'
    '                        if _it.get("status") == "ACTIVE" and _it.get("image"):\n'
    '                            pick = _it\n'
    '                            break\n'
    '                except Exception:\n'
    '                    pass\n'
    '\n'
    '            if pick:\n'
    '                _img = pick.get("image", "")\n'
    '                _nm  = pick.get("name", "")\n'
    '                _CATEGORY_IMAGE_CACHE[key] = {"ts": time.time(), "image": _img, "name": _nm}\n'
    '                result[key] = {"image": _img, "name": _nm, "emoji": cat.get("emoji", "")}\n'
    '                continue\n'
    '\n'
    '            # -- FALLBACK 3: curated stock image --\n'
    '            fallback_img = FALLBACK_CATEGORY_IMAGES.get(key, "")\n'
    '            if fallback_img:\n'
    '                _CATEGORY_IMAGE_CACHE[key] = {"ts": time.time(), "image": fallback_img, "name": cat["label"]}\n'
    '                result[key] = {"image": fallback_img, "name": cat["label"], "emoji": cat.get("emoji", "")}\n'
    '                continue\n'
    '\n'
    '            # -- final resort: emoji only --\n'
    '            result[key] = {"image": "", "name": "", "emoji": cat.get("emoji", "")}\n'
)

if "FALLBACK 3: curated stock image" in src:
    log.append("P3 already present")
elif old_block in src:
    src = src.replace(old_block, new_block, 1)
    log.append("P3 OK  -> endpoint fallbacks added")
else:
    log.append("P3 SKIP -> anchor not found")

# ---------- P4: warmer covers all categories ----------
old_warm = (
    '            PRIORITY_KEYWORDS = [\n'
    '                "smartphone", "smart tv", "home appliance", "beauty products",\n'
    '                "laptop", "fashion", "home kitchen", "gaming console",\n'
    '            ]\n'
)

new_warm = (
    '            _PRIO_KEYS = {"phones","tv","appliances","health",\n'
    '                          "home","fashion","computing","gaming"}\n'
    '            _prio = [c["query"] for c in CATEGORY_GROUPS if c["key"] in _PRIO_KEYS]\n'
    '            _rest = [c["query"] for c in CATEGORY_GROUPS if c["key"] not in _PRIO_KEYS]\n'
    '            PRIORITY_KEYWORDS = _prio + _rest\n'
)

if "Warming cache (all categories)" in src:
    log.append("P4 already present")
elif old_warm in src:
    src = src.replace(old_warm, new_warm, 1)
    src = src.replace(
        'print(f"[PSC] Warming cache (priority keywords first)...")',
        'print(f"[PSC] Warming cache (all categories)...")',
        1
    )
    log.append("P4 OK  -> warmer covers all 25 categories")
else:
    log.append("P4 SKIP -> warmer anchor not found")

# ---------- Write only if syntax stays valid ----------
if src == orig:
    print("No changes made.")
    sys.exit(0)

try:
    ast.parse(src)
except SyntaxError as e:
    print("PATCHED CODE HAS SYNTAX ERROR -- NOT WRITING.")
    print("  line " + str(e.lineno) + ": " + str(e.msg))
    sys.exit(1)

backup = TARGET + ".bak_p34_" + time.strftime("%Y%m%d_%H%M%S")
shutil.copy2(TARGET, backup)

with io.open(TARGET, "w", encoding=ENC, newline="\n") as f:
    f.write(src)

print("Applied to: " + TARGET)
print("Backup    : " + backup)
for line in log:
    print("  " + line)
print("Syntax: OK")
