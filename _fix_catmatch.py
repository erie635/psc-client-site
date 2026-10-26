import io, shutil, time, ast, os
os.chdir(r"C:\Users\erick\Desktop\PSC_Client_Site")
f = "client_app.py"
src = io.open(f, "r", encoding="utf-8-sig").read()
orig = src

# --- Fix A: FAST PATH 2 requires product keyword match ---
OLD_A = (
    '            pick = None\n'
    '            for p in products:\n'
    '                if p and p.get("image"):\n'
    '                    pick = p\n'
    '                    break\n'
)
NEW_A = (
    '            pick = None\n'
    '            _kw = [w for w in cat["query"].lower().split() if len(w) >= 3]\n'
    '            for p in products:\n'
    '                if not p or not p.get("image"):\n'
    '                    continue\n'
    '                if _kw:\n'
    '                    _hay = (str(p.get("name", "")) + " " +\n'
    '                            str(p.get("category", ""))).lower()\n'
    '                    if not any(w in _hay for w in _kw):\n'
    '                        continue\n'
    '                pick = p\n'
    '                break\n'
)
if OLD_A in src:
    src = src.replace(OLD_A, NEW_A, 1)
    print("Fix A (FAST PATH 2): OK")
else:
    print("Fix A (FAST PATH 2): SKIP")

# --- Fix B: FALLBACK 2 seller items must match category ---
OLD_B = (
    '            # -- FALLBACK 2: seller items --\n'
    '            if not pick:\n'
    '                try:\n'
    '                    for _it in _load_seller_items():\n'
    '                        if _it.get("status") == "ACTIVE" and _it.get("image"):\n'
    '                            pick = _it\n'
    '                            break\n'
    '                except Exception:\n'
    '                    pass\n'
)
NEW_B = (
    '            # -- FALLBACK 2: seller items that MATCH the category --\n'
    '            if not pick:\n'
    '                try:\n'
    '                    for _it in _load_seller_items():\n'
    '                        if _it.get("status") != "ACTIVE" or not _it.get("image"):\n'
    '                            continue\n'
    '                        if (str(_it.get("category_query", "")).lower() == cat["query"].lower()\n'
    '                                or str(_it.get("category_key", "")).lower() == cat["key"].lower()):\n'
    '                            pick = _it\n'
    '                            break\n'
    '                        _hay2 = (str(_it.get("name", "")) + " " +\n'
    '                                 str(_it.get("description", "")) + " " +\n'
    '                                 " ".join(str(k) for k in (_it.get("keywords") or []))).lower()\n'
    '                        if _kw and any(w in _hay2 for w in _kw):\n'
    '                            pick = _it\n'
    '                            break\n'
    '                except Exception:\n'
    '                    pass\n'
)
if OLD_B in src:
    src = src.replace(OLD_B, NEW_B, 1)
    print("Fix B (FALLBACK 2 seller): OK")
else:
    print("Fix B (FALLBACK 2 seller): SKIP")

if src == orig:
    print("No changes made.")
    raise SystemExit(1)

try:
    ast.parse(src)
except SyntaxError as e:
    print("SYNTAX ERROR line " + str(e.lineno) + ": " + str(e.msg))
    raise SystemExit(1)

bak = f + ".bak_catmatch_" + time.strftime("%Y%m%d_%H%M%S")
shutil.copy2(f, bak)
io.open(f, "w", encoding="utf-8", newline="\n").write(src)

print("Written: " + f)
print("Backup : " + bak)
print("Syntax OK")
