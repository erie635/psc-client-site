import re
from pathlib import Path

p = Path("client_app.py")
src = p.read_text(encoding="utf-8")

# This regex finds "emoji": "anything" and replaces it with "emoji": ""
# It safely ignores the other keys like "label" or "query"
new_src, count = re.subn(r'"emoji":\s*"[^"]*"', '"emoji": ""', src)

if count > 0:
    p.write_text(new_src, encoding="utf-8")
    print(f"OK: Successfully removed {count} emojis from client_app.py")
else:
    print("No emojis found to remove.")
