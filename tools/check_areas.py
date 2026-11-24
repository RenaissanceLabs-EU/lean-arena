import json, sys, re, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
msc = {a["code"]: a for a in json.load(open(os.path.join(ROOT, "data/msc.json"), encoding="utf-8"))}
BAD = ["—", "–", "!", "$", "fascinating", "beautiful", "powerful", "elegant", "crucial", "Lean ", "formalized", "formalised"]
def words(s): return len(re.sub(r"\\\(.*?\\\)", "x", s).split())
def check(code):
    p = os.path.join(ROOT, "data/areas", code + ".json"); errs = []
    try: a = json.load(open(p, encoding="utf-8"))
    except Exception as e: return ["cannot load: %s" % e]
    def need(c, m):
        if not c: errs.append(m)
    need(a.get("code") == code, "code mismatch")
    need(isinstance(a.get("short"), str) and 0 < len(a["short"]) <= 24, "short length")
    need(isinstance(a.get("hook"), str) and 20 <= len(a["hook"]) <= 130, "hook length %s" % len(a.get("hook", "")))
    ab = a.get("about", [])
    need(isinstance(ab, list) and len(ab) == 2 and all(40 <= words(x) <= 80 for x in ab), "about: two paragraphs of 45 to 75 words, got %s" % [words(x) for x in ab])
    ex = a.get("example", {})
    need(isinstance(ex, dict) and ex.get("title") and 35 <= words(ex.get("text", "")) <= 90, "example length %s" % words(ex.get("text", "")))
    ob = a.get("objects", [])
    need(5 <= len(ob) <= 7 and all(o.get("term") and o.get("gloss") and words(o["gloss"]) <= 20 for o in ob), "objects")
    th = a.get("theorems", [])
    need(4 <= len(th) <= 6 and all(t.get("name") and t.get("statement") and (t.get("year") is None or isinstance(t.get("year"), int)) and "year" in t for t in th), "theorems")
    op = a.get("open", None)
    need(isinstance(op, list) and len(op) <= 3 and all(o.get("name") and o.get("gloss") for o in op), "open")
    us = a.get("uses", [])
    need(2 <= len(us) <= 4 and all(isinstance(u, str) for u in us), "uses")
    li = a.get("links", [])
    need(3 <= len(li) <= 6 and all(l in msc and l != code for l in li), "links %s" % li)
    blob = json.dumps(a, ensure_ascii=False)
    for b in BAD:
        if b in blob: errs.append("contains %r" % b)
    need(blob.count("\\\\(") == blob.count("\\\\)"), "unbalanced math delimiters")
    return errs
if __name__ == "__main__":
    codes = sys.argv[1:] or sorted(msc); bad = 0
    for c in codes:
        e = check(c); print(c, "ok" if not e else "FAIL " + "; ".join(e)); bad += bool(e)
    sys.exit(1 if bad else 0)
