import io, re, ast, shutil, time, os
os.chdir(r"C:\Users\erick\Desktop\PSC_Client_Site")
f = "client_app.py"
src = io.open(f, "r", encoding="utf-8-sig").read()

NEW = """CATEGORY_GROUPS = [
    {"key": "phones", "label": "Phones & Tablets", "query": "smartphone", "emoji": "\U0001F4F1"},
    {"key": "tv", "label": "TVs & Audio", "query": "smart tv", "emoji": "\U0001F4FA"},
    {"key": "appliances", "label": "Appliances", "query": "home appliance", "emoji": "\U0001F50C"},
    {"key": "health", "label": "Health & Beauty", "query": "beauty products", "emoji": "\U0001F484"},
    {"key": "home", "label": "Home & Office", "query": "home kitchen", "emoji": "\U0001F3E0"},
    {"key": "fashion", "label": "Fashion", "query": "fashion", "emoji": "\U0001F455"},
    {"key": "computing", "label": "Computing", "query": "laptop", "emoji": "\U0001F4BB"},
    {"key": "gaming", "label": "Gaming", "query": "gaming console", "emoji": "\U0001F3AE"},
    {"key": "groceries", "label": "Groceries", "query": "groceries", "emoji": "\U0001F6D2"},
    {"key": "baby", "label": "Baby Products", "query": "baby products", "emoji": "\U0001F37C"},
    {"key": "sports", "label": "Sporting Goods", "query": "sports equipment", "emoji": "\u26BD"},
    {"key": "books", "label": "Books", "query": "books", "emoji": "\U0001F4DA"},
    {"key": "food", "label": "Food & Pantry", "query": "food", "emoji": "\U0001F37D\uFE0F"},
    {"key": "unga", "label": "Unga & Flour", "query": "flour", "emoji": "\U0001F33E"},
    {"key": "sugar", "label": "Sugar & Sweeteners", "query": "sugar", "emoji": "\U0001F36C"},
    {"key": "rice", "label": "Rice & Grains", "query": "rice", "emoji": "\U0001F35A"},
    {"key": "cooking_oil", "label": "Cooking Oil", "query": "cooking oil", "emoji": "\U0001FAD2"},
    {"key": "cereals", "label": "Cereals & Breakfast", "query": "cereal", "emoji": "\U0001F963"},
    {"key": "snacks", "label": "Snacks & Biscuits", "query": "biscuits", "emoji": "\U0001F36A"},
    {"key": "beverages", "label": "Beverages & Drinks", "query": "drinks", "emoji": "\U0001F964"},
    {"key": "dairy", "label": "Dairy & Eggs", "query": "milk", "emoji": "\U0001F95B"},
    {"key": "meat", "label": "Meat & Fish", "query": "chicken", "emoji": "\U0001F969"},
    {"key": "vegetables", "label": "Vegetables & Fruits", "query": "vegetables", "emoji": "\U0001F96C"},
    {"key": "spices", "label": "Spices & Condiments", "query": "spices", "emoji": "\U0001F9C2"},
    {"key": "canned", "label": "Canned & Packaged", "query": "canned beans", "emoji": "\U0001F96B"},
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
}"""

pat = re.compile(r"CATEGORY_GROUPS\s*=\s*\[.*?\n\]", re.DOTALL)
m = pat.search(src)
if not m:
    print("SKIP: anchor not found")
    raise SystemExit(1)

src = src[:m.start()] + NEW + src[m.end():]

try:
    ast.parse(src)
except SyntaxError as e:
    print("SYNTAX ERROR line " + str(e.lineno) + ": " + str(e.msg))
    raise SystemExit(1)

bak = f + ".bak_p12_" + time.strftime("%Y%m%d_%H%M%S")
shutil.copy2(f, bak)
io.open(f, "w", encoding="utf-8", newline="\n").write(src)

print("Written: " + f)
print("Backup : " + bak)
print("P1+P2 applied. Syntax OK")
