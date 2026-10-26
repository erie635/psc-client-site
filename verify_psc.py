import sys
from pathlib import Path

DIR = Path(r"C:\Users\erick\Desktop\PSC_Client_Site")
backups = sorted(DIR.glob("client_app.py.bak-*"), key=lambda p: p.stat().st_mtime)
orig_path = backups[-1]
new_path  = DIR / "client_app.py"

orig = orig_path.read_text(encoding="utf-8-sig")
new  = new_path.read_text(encoding="utf-8")

print("Backup:  " + orig_path.name + "  (" + str(len(orig)) + " chars)")
print("Patched: " + new_path.name  + "  (" + str(len(new)) + " chars)")
print()

SEM_START = "\n# === PSC PATCH: PLAYWRIGHT SEMAPHORE"
SEM_END   = "# === END PSC PATCH: PLAYWRIGHT SEMAPHORE ===\n\n"
VEN_START = "\n\n# === PSC PATCH: VENDOR TRIM (C) ==="

i = new.find(SEM_START)
j = new.find(SEM_END, i) + len(SEM_END)
k = new.find(VEN_START, j)

if i < 0 or j <= i or k < 0:
    print("FAIL: patch markers not found.")
    sys.exit(1)

stripped = new[:i] + new[j:k]

if stripped == orig:
    print("VERDICT: 100% SAFE.")
    print("  Strip the two PSC PATCH blocks and you get the original byte-for-byte.")
    print("  Your logic is untouched.")
    print("  SEM block:    " + str(j - i) + " chars inserted")
    print("  VENDOR block: " + str(len(new) - k) + " chars appended")
else:
    n = min(len(stripped), len(orig))
    for idx in range(n):
        if stripped[idx] != orig[idx]:
            print("First diff at char " + str(idx))
            print("  orig: " + repr(orig[max(0,idx-40):idx+40]))
            print("  new:  " + repr(stripped[max(0,idx-40):idx+40]))
            break
    else:
        print("Same up to " + str(n) + " chars, lengths " + str(len(stripped)) + " vs " + str(len(orig)))
