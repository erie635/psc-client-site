import io, shutil, time, ast, os
os.chdir(r"C:\Users\erick\Desktop\PSC_Client_Site")
f = "client_app.py"
src = io.open(f, "r", encoding="utf-8-sig").read()

OLD = (
    '            # -- FALLBACK 1: any product in memory with an image --\n'
    '            if not pick:\n'
    '                for _p in _PRODUCT_CACHE.values():\n'
    '                    if _p and _p.get("image"):\n'
    '                        pick = _p\n'
    '                        break\n'
)

NEW = (
    '            # -- FALLBACK 1: only a product that MATCHES this category --\n'
    '            if not pick:\n'
    '                _kw = [w for w in cat["query"].lower().split() if len(w) >= 3]\n'
    '                for _p in _PRODUCT_CACHE.values():\n'
    '                    if not _p or not _p.get("image"):\n'
    '                        continue\n'
    '                    _hay = (str(_p.get("name", "")) + " " +\n'
    '                            str(_p.get("category", ""))).lower()\n'
    '                    if _kw and all(w in _hay for w in _kw):\n'
    '                        pick = _p\n'
    '                        break\n'
)

if OLD not in src:
    print("SKIP: FALLBACK 1 block not found -- nothing changed")
    raise SystemExit(1)

src = src.replace(OLD, NEW, 1)

try:
    ast.parse(src)
except SyntaxError as e:
    print("SYNTAX ERROR line " + str(e.lineno) + ": " + str(e.msg))
    raise SystemExit(1)

bak = f + ".bak_f1b_" + time.strftime("%Y%m%d_%H%M%S")
shutil.copy2(f, bak)
io.open(f, "w", encoding="utf-8", newline="\n").write(src)

print("Written: " + f)
print("Backup : " + bak)
print("F1 fixed -- category images now match the category. Syntax OK")
