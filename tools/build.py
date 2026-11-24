#!/usr/bin/env python3
"""Build the Renaissance Labs Mathematics site into site/.

  python3 tools/build.py

Inputs: data/msc.json (MSC2020 areas), data/areas/*.json (area pages, hand-written),
data/coverage.json (tools/mathlib_coverage.py), envs/*/env.toml + gen.py (Lean environments).
Math is rendered to HTML at build time with KaTeX (node). Python 3.9, standard library only.
"""
import hashlib, html, json, math, os, re, shutil, subprocess, sys
from datetime import date

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
OUT = os.path.join(ROOT, "docs")
SITE = "https://math.renaissancelabs.eu"
MATHLIB = "https://github.com/leanprover-community/mathlib4"
LEAN_VERSION = "4.29.1"
e = html.escape

# ---------------------------------------------------------------- data
MSC = json.load(open(os.path.join(ROOT, "data/msc.json"), encoding="utf-8"))
AREAS = {a["code"]: a for a in MSC}
PAGES = {}
for c in AREAS:
    p = os.path.join(ROOT, "data/areas", c + ".json")
    if os.path.exists(p): PAGES[c] = json.load(open(p, encoding="utf-8"))
COV = json.load(open(os.path.join(ROOT, "data/coverage.json"), encoding="utf-8"))
BASE = json.load(open(os.path.join(ROOT, "data/baseline.json"), encoding="utf-8")) if os.path.exists(os.path.join(ROOT, "data/baseline.json")) else {}
GROUPS = [
    ("meta", "About mathematics", ["00", "01", "97"]),
    ("logic", "Logic and foundations", ["03", "06", "08", "18"]),
    ("algebra", "Algebra", ["12", "13", "15", "16", "17", "19", "20", "22"]),
    ("number", "Numbers and discrete structures", ["05", "11"]),
    ("analysis", "Analysis", ["26", "28", "30", "31", "32", "33", "34", "35", "37", "39", "40", "41", "42", "43", "44", "45", "46", "47", "49"]),
    ("geometry", "Geometry and topology", ["14", "51", "52", "53", "54", "55", "57", "58"]),
    ("computation", "Probability, statistics and computation", ["60", "62", "65", "68", "90", "93", "94"]),
    ("science", "Physical, life and social sciences", ["70", "74", "76", "78", "80", "81", "82", "83", "85", "86", "91", "92"]),
]
assert sorted(c for _, _, cs in GROUPS for c in cs) == sorted(AREAS), "group list does not match MSC"
GROUP_OF = {c: (i, g[0], g[1]) for i, g in enumerate(GROUPS) for c in g[2]}

VIZ = {}
# Only figures listed in viz/approved.json ship: each is reviewed by a person (or by me against the screenshots and the maths) first.
APPROVED = set(json.load(open(os.path.join(ROOT, "viz", "approved.json"), encoding="utf-8")))
vdir = os.path.join(ROOT, "viz", "meta")
if os.path.isdir(vdir):
    for fn in sorted(os.listdir(vdir)):
        if fn.endswith(".json"):
            m_ = json.load(open(os.path.join(vdir, fn), encoding="utf-8"))
            if m_["id"] in APPROVED and os.path.exists(os.path.join(ROOT, "viz", m_["id"] + ".js")): VIZ[m_["code"]] = m_

def read_toml(path):
    out = {}
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line: continue
        k, v = line.split("=", 1); out[k.strip()] = json.loads(v.strip())
    return out

ENVS = []
edir = os.path.join(ROOT, "envs")
for d in sorted(os.listdir(edir)):
    tp = os.path.join(edir, d, "env.toml")
    if not os.path.exists(tp): continue
    meta = read_toml(tp); meta["folder"] = d
    meta["slug"] = meta["name"]
    ENVS.append(meta)
TRAIN, EVAL = 84, 24

BASE_C = sum(v["closed"] for e_ in BASE.values() for v in e_.values()); BASE_N = sum(v["tasks"] for e_ in BASE.values() for v in e_.values())
def area_label(c): return PAGES[c]["short"] if c in PAGES else AREAS[c]["name"]
def cov(c): return COV["areas"][c]["theorems"]
RANK = {c: i + 1 for i, c in enumerate(sorted(AREAS, key=lambda c: -cov(c)))}
MAXLOG = math.log10(max(cov(c) for c in AREAS) + 1)
def weight(c): return 0 if cov(c) == 0 else int(10 + 52 * math.log10(cov(c) + 1) / MAXLOG)
def fmt(n): return "{:,}".format(int(n))

# ---------------------------------------------------------------- math
MATH_JOBS, MATH_INDEX = [], {}
MATH_RE = re.compile(r"\\\((.+?)\\\)|\\\[(.+?)\\\]", re.S)

def tx(s):
    """HTML-escape text and park its \\( \\) and \\[ \\] formulas as placeholders to be rendered later."""
    if not s: return ""
    out, pos = [], 0
    for m in MATH_RE.finditer(s):
        out.append(e(s[pos:m.start()]))
        tex, disp = (m.group(1), False) if m.group(1) is not None else (m.group(2), True)
        key = (tex.strip(), disp)
        if key not in MATH_INDEX:
            MATH_INDEX[key] = len(MATH_JOBS); MATH_JOBS.append({"tex": key[0], "display": disp})
        out.append("@@M%d@@" % MATH_INDEX[key]); pos = m.end()
    out.append(e(s[pos:]))
    return "".join(out)

def render_math():
    if not MATH_JOBS: return []
    r = subprocess.run(["node", os.path.join(ROOT, "tools/render_math.mjs")], input=json.dumps(MATH_JOBS), capture_output=True, text=True, cwd=ROOT)
    if r.returncode: raise SystemExit("KaTeX failed: " + r.stderr[-500:])
    res = json.loads(r.stdout); bad = [x for x in res if x.startswith("KATEX_ERROR")]
    if bad: raise SystemExit("KaTeX could not render:\n" + "\n".join(bad[:10]))
    return res

# ---------------------------------------------------------------- Lean highlighting
LEAN_KW = set("theorem lemma def example import open namespace end by fun have show from at with intro intros exact apply rw simp ring omega linarith nlinarith norm_num positivity field_simp induction cases rcases obtain refine use constructor rfl decide native_decide unfold sorry calc match if then else let in where structure instance class variable section noncomputable private protected abbrev inductive deriving only using".split())
LEAN_RE = re.compile(r"(/-.*?-/)|(--[^\n]*)|(\"(?:[^\"\\]|\\.)*\")|([A-Za-z_][A-Za-z_0-9.']*)", re.S)

def lean(code):
    out, pos = [], 0
    for m in LEAN_RE.finditer(code):
        out.append(e(code[pos:m.start()]))
        if m.group(1) or m.group(2): out.append('<span class="cm">%s</span>' % e(m.group(0)))
        elif m.group(3): out.append('<span class="st">%s</span>' % e(m.group(0)))
        else:
            w = m.group(4)
            out.append('<span class="kw">%s</span>' % e(w) if w in LEAN_KW else e(w))
        pos = m.end()
    out.append(e(code[pos:]))
    return "".join(out)

def codebox(code, lang="lean", copy=True):
    body = lean(code) if lang == "lean" else e(code)
    return '<div class="codebox">%s<pre>%s</pre></div>' % ('<button class="copy" type="button">Copy</button>' if copy else "", body)

# ---------------------------------------------------------------- page shell
VER = hashlib.md5((open(os.path.join(OUT, "styles.css"), "rb").read() + open(os.path.join(ROOT, "site_app.js"), "rb").read())).hexdigest()[:8]
IMPORTMAP = '<script type="importmap">{"imports":{"three":"/assets/three.module.min.js"}}</script>'
PAGES_OUT = {}
SITEMAP = []

def shell(path, title, desc, body, current="", math=False, viz=False):
    url = SITE + path
    seg = [x for x in path.split("/") if x]
    ogname = "home" if not seg else ("a" + seg[1] if seg[0] == "area" else "e" + seg[1] if seg[0] == "env" else seg[0])
    og = "%s/assets/og/%s.jpg" % (SITE, ogname)
    nav = [("/", "Map", "map"), ("/environments/", "Environments", "env"), ("/frontier/", "Frontier", "frontier"), ("/checking/", "How checking works", "check"), ("/about/", "About", "about")]
    links = "".join('<a href="%s"%s>%s</a>' % (h, ' aria-current="page"' if k == current else "", t) for h, t, k in nav)
    full = f'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{e(title)}</title>
<meta name="description" content="{e(desc)}">
<link rel="canonical" href="{url}">
<meta property="og:title" content="{e(title)}"><meta property="og:description" content="{e(desc)}"><meta property="og:url" content="{url}"><meta property="og:type" content="website">
<meta property="og:image" content="{og}"><meta property="og:image:width" content="1200"><meta property="og:image:height" content="630"><meta property="og:image:alt" content="{e(title)}"><meta property="og:site_name" content="Renaissance Labs Mathematics">
<meta name="twitter:card" content="summary_large_image"><meta name="twitter:image" content="{og}"><meta name="twitter:title" content="{e(title)}"><meta name="twitter:description" content="{e(desc)}"><meta name="theme-color" content="#fdfaf3">
<link rel="icon" href="/assets/favicon.png">
<link rel="stylesheet" href="/styles.css?v={VER}">
{'<link rel="stylesheet" href="/assets/katex.css">' if math else ''}
{IMPORTMAP if viz else ''}
<script>try{{var t=localStorage.getItem('theme');if(t)document.documentElement.dataset.theme=t}}catch(e){{}}</script>
</head>
<body>
<a class="skip" href="#main">Skip to content</a>
<header class="bar">
  <a class="brand" href="/"><img src="/assets/mark.png" alt=""><span>Renaissance Labs &middot; Mathematics</span></a>
  <nav>{links}<a class="ext" href="https://practice.renaissancelabs.eu">Practice</a><a class="ext" href="https://renaissancelabs.eu">Renaissance Labs</a></nav>
  <button class="theme" id="theme" type="button" aria-label="Toggle dark mode"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"><path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z"/></svg></button>
</header>
<main id="main">
{body}
</main>
<footer class="wrap foot">
  <a class="brand" href="https://renaissancelabs.eu"><img src="/assets/mark.png" alt="">Renaissance Labs</a>
  <div class="foot-links"><a href="/about/">About</a><a href="/data/areas.json">Data</a><a href="/llms.txt">llms.txt</a><a href="https://practice.renaissancelabs.eu">Practice</a><a href="https://labs.renaissancelabs.eu">Atlas</a><a href="https://huggingface.co/RenaissanceLabsEU">Hugging Face</a></div>
</footer>
<script src="/app.js?v={VER}" defer></script>
{'<script type="module" src="/viz/boot.js"></script>' if viz else ''}
</body>
</html>
'''
    PAGES_OUT[path] = full
    SITEMAP.append(url)

def wrap(inner, cls=""):
    return '<div class="wrap %s">%s</div>' % (cls, inner)

# ---------------------------------------------------------------- shared pieces
ENV_BY_AREA = {}
for m in ENVS: ENV_BY_AREA.setdefault(m["msc"], []).append(m)

def env_card(m):
    c = m["msc"]; gi = GROUP_OF[c][0]
    pills = "".join('<span class="pill">%s</span>' % e(x) for x in m.get("good_for", [])[:3])
    return f'''<a class="card b0{gi}" href="/env/{m["slug"]}/" style="--hue: var(--f0{gi})">
  <div class="top"><span class="fld"><i>{c}</i>{e(area_label(c))}</span><span>Lean 4</span></div>
  <h3>{e(m["title"])}</h3>
  <p class="sum">{e(m["summary"])}</p>
  <div class="facts">{pills}<span class="pill rw">reward 0 to 1</span></div>
  <div class="meta"><span><b>{TRAIN + EVAL}</b> tasks</span><span>{len(m["families"])} families</span></div>
</a>'''

def tile(c):
    gi = GROUP_OF[c][0]; n = cov(c); w = weight(c)
    subs = " ".join(s["name"].lower() for s in AREAS[c]["subareas"])
    page = PAGES.get(c, {})
    search = (AREAS[c]["name"] + " " + page.get("short", "") + " " + page.get("hook", "") + " " + subs + " " + " ".join(o["term"] for o in page.get("objects", []))).lower()
    has_env = c in ENV_BY_AREA
    dot = '<span class="envdot" title="Lean environment available"></span>' if has_env else ""
    vm = '<svg class="vzmark" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linejoin="round"><title>Interactive figure</title><path d="M12 3 4 7.5v9L12 21l8-4.5v-9z"/><path d="M4 7.5 12 12l8-4.5M12 12v9"/></svg>' if c in VIZ else ""
    dot = '<span class="tm">%s%s</span>' % (vm, dot) if (vm or dot) else ""
    cls = "tile" + (" empty" if n == 0 else "")
    return (f'<a class="{cls}" href="/area/{c}/" data-code="{c}" data-g="{GROUP_OF[c][1]}" data-s="{e(search)}" style="--w:{w}" title="{e(AREAS[c]["name"])}: {fmt(n)} theorems in Mathlib">'
            f'<span class="tc"><b>{c}</b>{dot}</span><span class="tn">{e(area_label(c))}</span>'
            f'<span class="tb"><i style="width:{w * 1.6:.0f}%"></i></span></a>')

def chips(codes):
    return "".join('<a class="chip b0%d" style="--hue: var(--f0%d)" href="/area/%s/"><i>%s</i>%s</a>' % (GROUP_OF[c][0], GROUP_OF[c][0], c, c, e(area_label(c))) for c in codes)

# ---------------------------------------------------------------- environment examples (generated)
EXAMPLES = {}
def load_examples():
    import importlib
    for m in ENVS:
        try: gen = importlib.import_module("envs.%s.gen" % m["folder"])
        except Exception as ex:
            print("cannot import", m["folder"], ex); continue
        per = []
        for fam in sorted(m["families"]):
            t = gen.generate(0, 2, fam); per.append((fam, t))
        EXAMPLES[m["slug"]] = {"main": gen.generate(1, 1), "families": per, "mod": gen}

def stmt_of(t):
    if t.kind == "define": return "def f (n : ℕ) : ℕ := sorry"
    return "theorem %s %s" % (t.theorems[0].name, t.theorems[0].statement.strip())

# ---------------------------------------------------------------- pages
def page_home():
    hundred = COV["hundred"]; h_ok = sum(1 for x in hundred if x["formalized"]); t_ok = COV["thousand"]["in_mathlib"]; t_all = COV["thousand"]["listed"]
    rows = []
    for gi, (gk, gname, codes) in enumerate(GROUPS):
        tot = sum(cov(c) for c in codes)
        rows.append(f'''<div class="row b0{gi}" data-g="{gk}" style="--hue: var(--f0{gi})">
  <a class="row-label" href="#map"><span class="code">{len(codes)} areas</span><span class="nm">{e(gname)}</span><span class="ct">{fmt(tot)} theorems</span></a>
  <div class="tiles">{"".join(tile(c) for c in codes)}</div></div>''')
    n_env = len(ENVS); n_tasks = n_env * (TRAIN + EVAL)
    covered = sorted(ENV_BY_AREA)
    cards = "".join(env_card(m) for m in ENVS) or '<p class="none">The first environments are on their way.</p>'
    body = f'''
<section class="intro">
  <p class="eyebrow">Renaissance Labs &middot; Mathematics</p>
  <h1>All of mathematics, <em>mapped</em> and <em>formalized</em>.</h1>
  <p class="lede">Every field of mathematics in one place: what it studies, what it has proved, how much of it a computer can already check, and Lean environments where intelligence learns to prove the rest.</p>
  <div class="stats">
    <div class="stat"><b>{len(AREAS)}</b><span>areas</span></div>
    <div class="stat"><b>{sum(len(a["subareas"]) for a in MSC)}</b><span>subareas</span></div>
    <div class="stat"><b>{fmt(COV["mathlib_theorems"])}</b><span>theorems in Mathlib</span></div>
    <div class="stat"><b>{len(VIZ)}</b><span>interactive {"figure" if len(VIZ) == 1 else "figures"}</span></div>
    <div class="stat"><b>{n_env}</b><span>Lean environments</span></div>
    <div class="stat"><b>{fmt(n_tasks)}</b><span>checked tasks</span></div>
  </div>
</section>
<div class="wrap">
  <div class="chart-head" id="map">
    <div><h2>The map</h2><p>The 63 areas of the Mathematics Subject Classification (MSC2020), the system mathematicians use to file their papers. Shading shows how much of each area Mathlib, the main Lean library, already contains. Open a tile to see what the area is about, its landmark theorems and its open problems.</p></div>
    <div class="scale"><span>less in Lean</span><i style="opacity:.25"></i><i style="opacity:.55"></i><i></i><span>more</span><i class="e"></i><span>almost nothing yet</span><span class="envdot"></span><span>environment</span><svg class="vzmark" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linejoin="round"><path d="M12 3 4 7.5v9L12 21l8-4.5v-9z"/><path d="M4 7.5 12 12l8-4.5M12 12v9"/></svg><span>interactive figure</span></div>
  </div>
  <div class="mapsearch"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="11" cy="11" r="7"/><path d="m20 20-3.5-3.5"/></svg><input id="q" type="search" placeholder="Search 534 subareas: elliptic curves, homotopy, Markov chains…" autocomplete="off" aria-label="Search areas"><span id="qn"></span></div>
  <div class="chart" id="chart">{"".join(rows)}</div>

  <section class="gap-sec">
    <div class="three">
      <a class="path" href="#envs"><p class="eyebrow">For models</p><h3>Practice proving</h3><p>Lean environments that generate fresh, checked problems in {n_env} areas, with a reward from the Lean kernel.</p></a>
      <a class="path" href="/frontier/"><p class="eyebrow">For the field</p><h3>See the frontier</h3><p>{h_ok} of Freek Wiedijk's 100 famous theorems are formalized. Of the 1000+ project's {fmt(t_all)} theorems, {t_ok} are in Mathlib.</p></a>
      <a class="path" href="/checking/"><p class="eyebrow">For trust</p><h3>How a proof is checked</h3><p>What counts as proved, and the cheating attempts the checker was tested against.</p></a>
    </div>
  </section>

  <section class="house-sec" id="envs">
    <div class="house-head"><div><p class="eyebrow">Environments</p><h2>Where intelligence practices mathematics</h2>
    <p>Each environment generates tasks in one area. The agent edits a Lean file; the Lean kernel gives the reward. The checks cannot be argued with, and the supply of problems does not run out.</p></div>
    <a class="btn ghost" href="/environments/">All environments</a></div>
    <div class="grid" style="margin-top:22px">{cards}</div>
  </section>

  <section class="flywheel">
    <h2>One loop, two outcomes</h2>
    <p class="lede2">Better intelligence formalizes more mathematics. More formalized mathematics makes better environments. Each turn of the loop leaves behind verified results anyone can use.</p>
    <ol class="steps">
      <li><span>1</span><div><b>Map</b><p>Every area, filed by MSC2020, with its Mathlib coverage measured from source.</p><em class="live">Live</em></div></li>
      <li><span>2</span><div><b>Environments</b><p>Generated Lean tasks with a kernel-checked reward, in {n_env} areas so far, growing.</p><em class="live">Live</em></div></li>
      <li><span>3</span><div><b>Formalizer</b><p>Agents that read the literature and write the missing definitions and theorems in Lean.</p><em class="next">Next</em></div></li>
      <li><span>4</span><div><b>Models</b><p>Open models trained on the environments, with public curves of what improves.</p><em class="next">Next</em></div></li>
    </ol>
  </section>
</div>'''
    shell("/", "Renaissance Labs Mathematics: all of mathematics, mapped and formalized", "A map of all 63 areas of mathematics with Lean formalization coverage, and Lean environments where models practice proving, checked by the Lean kernel.", body, "map", math=False)

def page_area(c):
    a = AREAS[c]; p = PAGES.get(c); gi, gk, gname = GROUP_OF[c]; n = cov(c); co = COV["areas"][c]
    codes = [x for x in sorted(AREAS)]; i = codes.index(c)
    prev = codes[i - 1] if i else None; nxt = codes[i + 1] if i + 1 < len(codes) else None
    subs = "".join('<li><i>%s</i>%s</li>' % (s["code"], e(s["name"])) for s in a["subareas"]) or '<li class="faint">No second-level classes.</li>'
    hook = tx(p["hook"]) if p else ""
    if p:
        about = "".join("<p>%s</p>" % tx(t) for t in p["about"])
        ex = p["example"]
        objects = "".join('<div><dt>%s</dt><dd>%s</dd></div>' % (tx(o["term"]), tx(o["gloss"])) for o in p["objects"])
        theorems = "".join('<li><div class="th-h"><b>%s</b>%s</div><p>%s</p></li>' % (tx(t["name"]), ('<span class="yr">%s</span>' % t["year"]) if t.get("year") else "", tx(t["statement"])) for t in p["theorems"])
        openp = "".join('<li><b>%s</b><p>%s</p></li>' % (tx(o["name"]), tx(o["gloss"])) for o in p["open"])
        uses = "".join("<li>%s</li>" % tx(u) for u in p["uses"])
        related = chips(p["links"])
    mlinks = "".join('<li><a href="%s/tree/%s/Mathlib/%s">Mathlib/%s</a><span>%s</span></li>' % (MATHLIB, COV["mathlib_commit"], d["dir"], d["dir"], fmt(d["theorems"])) for d in co["dirs"])
    if n == 0:
        covtxt = '<p class="covbig"><b>almost nothing yet</b></p><p class="note">Mathlib has little or no material filed under this area. That makes it a place where new formalization has the most to add.</p>'
    else:
        covtxt = f'<p class="covbig"><b>{fmt(n)}</b> theorems <span class="faint">&middot; ranked {RANK[c]} of {len(AREAS)}</span></p><div class="bigbar"><i style="width:{weight(c) * 1.6:.0f}%"></i></div><ul class="mods">{mlinks}</ul>'
    v = VIZ.get(c)
    viz_html = ""
    if v:
        notice = "".join("<li>%s</li>" % tx(x) for x in v["notice"])
        viz_html = (f'''<section class="sec vizsec" aria-labelledby="viz-h"><p class="eyebrow">Interactive</p><h2 id="viz-h">{tx(v["title"])}</h2>
<p class="vz-lede">{tx(v["lede"])}</p>
<figure class="vz" data-viz="{v["id"]}"><div class="vz-stage" role="img" aria-label="{e(v["title"])}"></div><div class="vz-controls"></div><figcaption><span class="vz-hint">{e(v["hint"])}</span></figcaption>
<noscript><p class="vz-fail">This figure needs JavaScript.</p></noscript></figure>
<div class="vz-notice"><b>What to notice</b><ul>{notice}</ul></div></section>''')
    envs = ENV_BY_AREA.get(c, [])
    if envs: envhtml = '<div class="grid">%s</div>' % "".join(env_card(m) for m in envs)
    else: envhtml = '<div class="open-env"><p>No environment in this area yet. Each environment is a generator of Lean tasks with a verifier: see how they are built and add one.</p><a class="btn ghost" href="/about/#contribute">Contribute an environment</a></div>'
    pager = "".join('<a href="/area/%s/">%s <b>%s</b> %s</a>' % (x, arrow_l if k == 0 else "", "%s %s" % (x, e(area_label(x))), arrow_r if k else "") for k, x in enumerate([prev, nxt]) if x) if True else ""
    if p:
        main = f'''
<div class="area">
  <div class="area-main">
    <div class="sec">{about}</div>
    <div class="sec taste"><h2>{e(ex["title"])}</h2><p>{tx(ex["text"])}</p></div>
    {viz_html}
    <div class="sec"><h2>Central objects</h2><dl class="objects">{objects}</dl></div>
    <div class="sec"><h2>Landmark theorems</h2><ol class="thms">{theorems}</ol></div>
    {('<div class="sec"><h2>Open problems and frontiers</h2><ul class="openp">%s</ul></div>' % openp) if p["open"] else ""}
    <div class="sec"><h2>Environments in this area</h2>{envhtml}</div>
  </div>
  <aside class="area-side">
    <div class="panel"><p class="eyebrow">In Lean today</p>{covtxt}</div>
    <div class="panel"><p class="eyebrow">Where it shows up</p><ul class="uses">{uses}</ul></div>
    <div class="panel"><p class="eyebrow">Neighbors</p><div class="chips">{related}</div></div>
    <div class="panel"><p class="eyebrow">Subareas, MSC {c}</p><ul class="subs">{subs}</ul></div>
  </aside>
</div>'''
    else:
        main = '<p class="lede">This page is being written.</p>'
    body = f'''
<div class="wrap b0{gi}" style="--hue: var(--f0{gi})">
  <nav class="crumbs"><a href="/">Map</a><span>/</span><a href="/#map">{e(gname)}</a><span>/</span><span>MSC {c}</span></nav>
  <header class="area-head"><p class="eyebrow"><span class="codepill">{c}</span> {e(a["name"])}</p>
  <h1>{e(area_label(c)) if p else e(a["name"])}</h1>
  <p class="hook">{hook}</p></header>
  {main}
  <nav class="pager">{pager}</nav>
</div>'''
    shell("/area/%s/" % c, "%s · Mathematics, mapped" % (area_label(c)), (p["hook"] if p else a["name"]).replace("\\(", "").replace("\\)", "")[:155], body, "map", math=True, viz=bool(v))

arrow_l = "&larr;"; arrow_r = "&rarr;"

def page_env(m):
    ex = EXAMPLES.get(m["slug"])
    if not ex: return
    c = m["msc"]; gi = GROUP_OF[c][0]; t = ex["main"]
    def fam_cell(tt):
        if tt.kind == "define": return '<p class="famdesc">%s</p>' % tx(tt.informal.split("\n\n")[-1])
        return codebox(stmt_of(tt), copy=False).replace('class="codebox"', 'class="codebox mini"')
    fam = "".join('<tr><td><b>%s</b></td><td>%s</td></tr>' % (e(f.replace("_", " ")), fam_cell(tt)) for f, tt in ex["families"])
    gf = "".join("<li>%s</li>" % e(x) for x in m.get("good_for", []))
    kind = m["kind"]
    check = ("Every theorem must be stated exactly as given and proved: no <code>sorry</code>, no new axioms, no <code>native_decide</code>. The reward is the share of theorems that pass." if kind == "prove" else
             "Your definition is run on hidden inputs: the grader proves a statement about <code>f</code> by evaluation and compares with the reference values. The reward is 1 if every value agrees, 0 otherwise.")
    slug = m["slug"]
    b = BASE.get(slug)
    if b:
        cells = "".join('<div><dt>Difficulty %s</dt><dd>%d of %d</dd></div>' % (k, v["closed"], v["tasks"]) for k, v in sorted(b.items()))
        tot_c = sum(v["closed"] for v in b.values()); tot_n = sum(v["tasks"] for v in b.values())
        hard = ('<div class="sec"><h2>How hard is it?</h2><p>A floor, not a ceiling: how many sampled tasks a single automation call can close with no thought at all. '
                'Each theorem was given the tactic <code>first | grind | aesop | simp | omega | norm_num | nlinarith | decide</code>. A task counts as closed only if every theorem in it is. '
                'Overall %d of %d. The rest need a real proof.</p><dl class="reward">%s</dl>'
                '<p class="note">Sample: 8 seeds at each difficulty. No model has been run on these tasks yet, so how hard they are for a model is not yet measured.</p></div>') % (tot_c, tot_n, cells)
    else: hard = ""
    cmd1 = codebox("git clone https://github.com/RenaissanceLabs-EU/lean-arena && cd lean-arena\ncd lean && lake exe cache get", "sh")
    cmd2 = codebox("python3 tools/make_task.py %s --seed 7 --difficulty 2 --out /tmp/task" % m["folder"], "sh")
    cmd3 = codebox("python3 arena/grade.py --spec /tmp/task/spec.json --solution /tmp/task/Solution.lean", "sh")
    start_box = codebox(t.start_file()); ref_box = codebox(t.reference_solution()); instr = instr_html(t)
    body = f'''
<div class="wrap b0{gi}" style="--hue: var(--f0{gi})">
  <nav class="crumbs"><a href="/environments/">Environments</a><span>/</span><a href="/area/{c}/">MSC {c} {e(area_label(c))}</a></nav>
  <header class="env-head"><a class="fldchip" href="/area/{c}/"><i>{c}</i><span>{e(AREAS[c]["name"])}</span></a>
  <h1>{e(m["title"])}</h1><p class="id">{e(slug)}</p><p class="lede">{e(m["summary"])}</p>
  <div class="actions"><a class="btn" href="#run">How to run it</a><a class="btn ghost" href="/checking/">How checking works</a></div></header>
  <div class="env">
    <div>
      <div class="sec"><h2>What the agent does</h2><p>The agent gets a working directory with a Lean file, <code>Solution.lean</code>, and a problem in words. It edits the file until it compiles and is correct. Tasks are generated from a seed and a difficulty from 1 to 3, so the supply is unlimited and every task is new.</p></div>
      <div class="sec"><h2>An example task</h2><div class="task"><div class="task-h">Instruction, as the agent sees it</div><div class="task-b prose2">{instr}</div></div>
      <div class="step"><div class="step-h"><b>Solution.lean</b><span>the file the agent starts from</span></div>{start_box}</div>
      <details class="ref"><summary>Show a reference solution</summary>{ref_box}<p class="note">Reference solutions are never shown to the agent. They are compiled in the environment's self-test, so every task has at least one proof that passes.</p></details></div>
      <div class="sec"><h2>The families</h2><p>Each task belongs to one family: a different piece of the area's work.</p><table class="t fam">{fam}</table></div>
      <div class="sec"><h2>Reward</h2><dl class="reward"><div><dt>Range</dt><dd>0 to 1</dd></div><div><dt>Checked by</dt><dd>Lean kernel</dd></div><div><dt>Deterministic</dt><dd>yes</dd></div></dl><p>{check} A file that does not compile scores 0. The submission is also re-checked by a second kernel run. Read <a href="/checking/">how checking works</a>.</p></div>
      <div class="sec" id="run"><h2>How to run it</h2>
        <div class="step"><div class="step-h"><b>1. Set up the Lean project</b><span>Lean {LEAN_VERSION} with Mathlib {COV["mathlib_commit"][:10]}</span></div>{cmd1}</div>
        <div class="step"><div class="step-h"><b>2. Generate a task</b><span>seed and difficulty pick the task</span></div>{cmd2}</div>
        <div class="step"><div class="step-h"><b>3. Grade a solution</b><span>prints the reward</span></div>{cmd3}</div>
        <p class="note">Tasks are also exported as Harbor task folders (<code>instruction.md</code>, <code>task.toml</code>, <code>tests/</code>), the format used by several RL frameworks, with the image built from the Lean project.</p></div>
      {hard}
      <div class="sec"><h2>Good for</h2><ul class="goodfor">{gf}</ul></div>
    </div>
    <aside class="side"><dl>
      <div><dt>Area</dt><dd><a href="/area/{c}/">MSC {c} &middot; {e(AREAS[c]["name"])}</a></dd></div>
      <div><dt>Skill</dt><dd>{e(m.get("skill", ""))}</dd></div>
      <div><dt>Kind</dt><dd>{"Prove theorems" if kind == "prove" else "Write definitions"}</dd></div>
      <div><dt>Tasks</dt><dd>{TRAIN} train, {EVAL} held-out eval, per export</dd></div>
      <div><dt>Families</dt><dd>{len(m["families"])}</dd></div>
      <div><dt>Difficulty</dt><dd>1 to 3, set by the generator</dd></div>
      <div><dt>Toolchain</dt><dd class="mono">Lean {LEAN_VERSION}<br>Mathlib {COV["mathlib_commit"][:10]}</dd></div>
    </dl></aside>
  </div>
</div>'''
    shell("/env/%s/" % slug, "%s · Lean environment · Renaissance Labs Mathematics" % m["title"], m["summary"], body, "env", math=True)

def instr_html(t):
    """The task instruction rendered from its Markdown subset: headings, paragraphs, bullets, formulas."""
    out, para, bullets = [], [], []
    def flush():
        nonlocal para, bullets
        if para: out.append("<p>%s</p>" % inline_code(" ".join(para))); para = []
        if bullets: out.append("<ul>%s</ul>" % "".join("<li>%s</li>" % inline_code(b) for b in bullets)); bullets = []
    text = t.instruction()
    for line in text.split("\n"):
        s = line.rstrip()
        if s.startswith("# "): flush(); out.append("<h4>%s</h4>" % e(s[2:]))
        elif s.startswith("## "): flush(); out.append("<h5>%s</h5>" % e(s[3:]))
        elif s.startswith("- "):
            if para: flush()
            bullets.append(s[2:])
        elif not s.strip(): flush()
        else: para.append(s)
    flush()
    return "".join(out).replace("<p>%s</p>" % "", "")

def inline_code(s):
    parts = re.split(r"(`[^`]+`)", s); out = []
    for q in parts:
        out.append("<code>%s</code>" % e(q[1:-1]) if q.startswith("`") and q.endswith("`") and len(q) > 2 else tx(q))
    return "".join(out)

def page_envs():
    cards = "".join(env_card(m) for m in ENVS)
    done = sorted(ENV_BY_AREA)
    missing = [c for c in sorted(AREAS) if c not in ENV_BY_AREA and c not in ("00", "01", "97")]
    body = f'''
<div class="wrap">
  <header class="page-head"><p class="eyebrow">Lean environments</p><h1>Environments</h1>
  <p class="lede">Generators of Lean tasks, one area of mathematics each. An agent edits a Lean file; the Lean kernel decides the reward. {len(ENVS)} environments cover {len(done)} of the {len(AREAS)} areas so far.</p></header>
  <div class="grid">{cards}</div>
  <section class="gap"><div><h3>Areas still waiting</h3><p>No environment here yet. Each is a chance to add one.</p></div>
  <ul>{"".join('<li><a href="/area/%s/"><i>%s</i>%s</a></li>' % (c, c, e(area_label(c))) for c in missing)}</ul></section>
</div>'''
    shell("/environments/", "Lean environments · Renaissance Labs Mathematics", "Generated Lean proving environments across areas of mathematics, with a kernel-checked reward.", body, "env")

def page_frontier():
    hundred = COV["hundred"]; h_ok = sum(1 for x in hundred if x["formalized"])
    rows = "".join('<tr class="%s"><td class="n">%d</td><td>%s</td><td>%s</td></tr>' % (
        "yes" if x["formalized"] else "no", x["n"], e(x["title"]),
        ('<span class="badge ok">%s</span>' % ("in Mathlib" if x["in_mathlib"] else "formalized outside Mathlib")) if x["formalized"] else '<span class="badge todo">not yet in Lean</span>') for x in hundred)
    def bars(lst):
        return "".join('<li><span>%s</span><div class="meter"><i style="width:%d%%"></i></div><b>%d / %d</b></li>' % (e(x["topic"]), round(100 * x["in_mathlib"] / max(1, x["items"])), x["in_mathlib"], x["items"]) for x in lst)
    t_ok, t_all = COV["thousand"]["in_mathlib"], COV["thousand"]["listed"]
    top = sorted(AREAS, key=lambda c: -cov(c))[:10]; low = [c for c in AREAS if cov(c) == 0]
    body = f'''
<div class="wrap">
  <header class="page-head"><p class="eyebrow">Formalization frontier</p><h1>What Lean knows, and what it does not yet</h1>
  <p class="lede">Three lists maintained by the Lean community measure how much of mathematics is formalized. Together with the area counts on the map, they show where the next theorems should come from.</p></header>
  <div class="frontier-stats">
    <div class="fs"><b>{h_ok}<small> / 100</small></b><span>of the 100 famous theorems formalized</span></div>
    <div class="fs"><b>{t_ok}<small> / {fmt(t_all)}</small></b><span>of the 1000+ list in Mathlib itself</span></div>
    <div class="fs"><b>{fmt(COV["mathlib_theorems"])}</b><span>theorems and lemmas in Mathlib</span></div>
    <div class="fs"><b>{len(low)}</b><span>areas with almost nothing in Mathlib</span></div>
  </div>
  <div class="one">
    <section class="sec"><h2>Undergraduate mathematics</h2><p>Mathlib's own checklist of the standard undergraduate curriculum, topic by topic: how many listed concepts have a Lean declaration.</p><ul class="meters">{bars(COV["undergrad"])}</ul></section>
  </div>
  <section class="sec"><h2>The 100 theorems</h2><p>Freek Wiedijk's list of <a href="https://www.cs.ru.nl/~freek/100/">100 famous theorems</a>, as tracked by Mathlib. {h_ok} have a formal proof in some Lean project; {sum(1 for x in hundred if x["in_mathlib"])} are inside Mathlib.</p>
  <table class="t hundred"><thead><tr><th>#</th><th>Theorem</th><th>Status</th></tr></thead><tbody>{rows}</tbody></table></section>
  <section class="sec"><h2>Where the gaps are widest</h2><p>Areas where Mathlib has almost nothing, by our mapping of Mathlib to MSC areas. Several are applied fields, where formalization is just beginning.</p>
  <div class="chips">{chips(low)}</div></section>
  <section class="sec"><h2>The 1000+ theorems project</h2><p>The <a href="https://1000-plus.github.io/">1000+ project</a> lists {fmt(t_all)} theorems across mathematics. {t_ok} of them have a declaration in Mathlib. Some of the rest are proved in other Lean projects or in other proof assistants; the figure here counts Mathlib only.</p></section>
  <p class="note">Source: Mathlib commit <span class="mono">{COV["mathlib_commit"][:10]}</span>, files <span class="mono">docs/100.yaml</span>, <span class="mono">docs/1000.yaml</span> and <span class="mono">docs/undergrad.yaml</span>.</p>
</div>'''
    shell("/frontier/", "Formalization frontier · Renaissance Labs Mathematics", "How much of mathematics is formalized in Lean: the 100 theorems, the 1000+ project, undergraduate coverage, and the widest gaps.", body, "frontier")

def page_checking():
    body = f'''
<div class="wrap">
  <header class="page-head"><p class="eyebrow">Trust</p><h1>How a proof is checked</h1>
  <p class="lede">An environment is only as good as its reward. Here is exactly what counts as proved, and what the checker was tested against.</p></header>
  <div class="prose">
    <h2>Why Lean makes a good reward</h2>
    <p>Lean has a small kernel that checks every proof step by step. If a theorem compiles with no gaps, it is true in the system, whoever or whatever wrote the proof. That gives a reward signal nobody has to judge by hand. What the kernel does not check is whether a statement means what a human intended. That is why each task shows the statement in words, and why statements are generated from fixed templates and not written by the model being trained.</p>
    <h2>The pipeline</h2>
    <ol class="flow">
      <li><b>Compile.</b> The submitted <span class="mono">Solution.lean</span> must compile against Mathlib. If it does not, the reward is 0.</li>
      <li><b>Re-check.</b> A second program, <span class="mono">leanchecker</span>, replays every declaration in the kernel from scratch. This catches proofs added to the environment by tricks that skip the kernel.</li>
      <li><b>Compare to the reference.</b> A small Lean program loads the hidden reference and the submission into two separate environments and compares kernel terms, not text. Nothing the submission defines can change how that comparison is read.</li>
      <li><b>Check axioms.</b> Each proof may rest on exactly three axioms that Mathlib itself uses: <span class="mono">propext</span>, <span class="mono">Classical.choice</span> and <span class="mono">Quot.sound</span>. Anything else, including <span class="mono">sorry</span>, fails.</li>
      <li><b>Score.</b> The reward is the weighted share of theorems that pass all of the above.</li>
    </ol>
    <h2>What the checker compares</h2>
    <ul>
      <li>Every definition the task provides must be unchanged: same kind, type and value.</li>
      <li>Every target theorem must have exactly the statement of the reference, as a kernel term.</li>
      <li>For tasks that ask the agent to write a definition, the type must match and the value is the agent's own; it is then tested by running it on hidden inputs.</li>
    </ul>
    <h2>Cheating attempts the checker was tested against</h2>
    <p>Each of these was written as a real submission and run through the grader. All were rejected.</p>
    <table class="t"><thead><tr><th>Attempt</th><th>Result</th></tr></thead><tbody>
      <tr><td>Leave a <span class="mono">sorry</span> in a proof</td><td>Rejected: depends on <span class="mono">sorryAx</span></td></tr>
      <tr><td>Prove by <span class="mono">native_decide</span></td><td>Rejected: adds a compiler axiom</td></tr>
      <tr><td>Change a provided definition and prove the new statement</td><td>Rejected: definition differs from the task's</td></tr>
      <tr><td>Prove a weaker statement under the same name</td><td>Rejected: statement differs from the one asked for</td></tr>
      <tr><td>Skip the kernel and add a false theorem straight into the environment</td><td>Rejected by the second kernel run</td></tr>
      <tr><td>Declare a new <span class="mono">axiom</span> and use it</td><td>Rejected: depends on an axiom that is not allowed</td></tr>
    </tbody></table>
    <h2>What this does not do</h2>
    <ul>
      <li>It does not judge whether a statement is interesting, only whether it is proved. Task statements come from reviewed generators, and every generator ships a reference proof that is compiled in its self-test.</li>
      <li>It does not measure difficulty for a given model. That needs baselines, which are published as they are run. What we have measured is a floor: on a sample of proving tasks, one automation call (<span class="mono">grind</span>, <span class="mono">aesop</span>, <span class="mono">simp</span> and similar) closes {BASE_C} of {BASE_N}, and each environment page shows its own figures.</li>
      <li>A proof that is correct but very slow can time out. Tasks have a time limit, stated in the task file.</li>
    </ul>
  </div>
</div>'''
    shell("/checking/", "How a proof is checked · Renaissance Labs Mathematics", "What counts as proved in the Lean environments: kernel re-check, term comparison, axiom check, and the cheating attempts tested.", body, "check")

def page_about():
    body = f'''
<div class="wrap">
  <header class="page-head"><p class="eyebrow">About</p><h1>A map, and a place to practice</h1></header>
  <div class="prose">
    <p>Renaissance Labs is the lab for frontier labs. We build the environments, evaluations and data that bring intelligence to every field of human work, and we give them away. This site is the mathematics part of that work.</p>
    <h2>The idea</h2>
    <p>Mathematics is the one field where an answer can be checked by machine with no judgment involved. That makes it the best place to learn how intelligence improves itself. This site has two halves that feed each other: a map of all of mathematics with its formalization status, and Lean environments that turn the gaps on the map into problems a model can practice on. As models get better at proving, they can formalize more of the map.</p>
    <h2>How the map is made</h2>
    <ul>
      <li><b>Structure.</b> The 63 areas and 534 subareas are the top two levels of the <a href="https://msc2020.org/">Mathematics Subject Classification 2020</a>, the scheme used by zbMATH Open and Mathematical Reviews. We use it unchanged, and group the areas into eight families for the map.</li>
      <li><b>Area pages.</b> Written for this site and checked for form by a script. Mathematical statements were written from memory by a language model and have not all been reviewed by specialists; years follow one convention noted on each page where it is ambiguous. Spot an error and tell us.</li>
      <li><b>Coverage.</b> Counted from the source of Mathlib at commit <span class="mono">{COV["mathlib_commit"][:10]}</span>: every <span class="mono">theorem</span> and <span class="mono">lemma</span> declaration, filed under MSC areas by a hand-written mapping of Mathlib directories (<span class="mono">tools/mathlib_coverage.py</span>). A directory that covers several areas is split evenly. This is a measure of size, not of depth, and the mapping is ours: a few areas show almost nothing because Mathlib has no directory for them, even though a result or two may exist elsewhere.</li>
      <li><b>Frontier lists.</b> Read directly from Mathlib's own tracking files.</li>
    </ul>
    <h2>Interactive figures</h2>
    <p>Some area pages carry a three.js figure you can drag and change. We add one only when it shows something prose cannot: how a matrix reshapes space, why a Lorenz trajectory cannot be predicted, what a Möbius strip does to an arrow. Most areas have none, on purpose; a figure that decorates is worse than none. Each one is computed from the mathematics, not animated by hand, and each caption states only what the figure shows. Everything runs in your browser and nothing is sent anywhere.</p>
    <h2 id="contribute">Add an environment</h2>
    <p>An environment is a Python generator that returns a Lean task: a statement with <span class="mono">sorry</span>, plus a reference proof. The contract is in <span class="mono">AUTHORING.md</span> in the repository. Good environments are true, varied, need a real idea at higher difficulty, and are not closed by a single automation call. Open a pull request.</p>
    <h2>Related</h2>
    <ul><li><a href="https://practice.renaissancelabs.eu">Practice</a>, the index of reinforcement learning environments for every field, and our own environments across 22 fields.</li><li><a href="https://labs.renaissancelabs.eu">The Atlas</a>, a map of open labs.</li><li><a href="https://learn.renaissancelabs.eu">Learn</a>, films and courses.</li></ul>
    <h2>Data</h2>
    <p><a href="/data/areas.json">areas.json</a> has all area pages, <a href="/data/coverage.json">coverage.json</a> the Mathlib measurements, <a href="/data/environments.json">environments.json</a> the environments. Released under CC BY 4.0; code under the MIT license.</p>
  </div>
</div>'''
    shell("/about/", "About · Renaissance Labs Mathematics", "How the mathematics map and the Lean environments are made, and where the numbers come from.", body, "about")

# ---------------------------------------------------------------- build
def main():
    load_examples()
    page_home(); page_envs(); page_frontier(); page_checking(); page_about()
    for c in AREAS: page_area(c)
    for m in ENVS: page_env(m)
    rendered = render_math()
    # clean generated dirs (keep assets, styles.css, app.js)
    for d in ("area", "env", "environments", "frontier", "checking", "about", "data", "viz"):
        shutil.rmtree(os.path.join(OUT, d), ignore_errors=True)
    for path, text in PAGES_OUT.items():
        text = re.sub(r"@@M(\d+)@@", lambda m: rendered[int(m.group(1))], text)
        fp = os.path.join(OUT, path.strip("/"), "index.html") if path != "/" else os.path.join(OUT, "index.html")
        os.makedirs(os.path.dirname(fp), exist_ok=True); open(fp, "w", encoding="utf-8").write(text)
    shutil.copy(os.path.join(ROOT, "site_app.js"), os.path.join(OUT, "app.js"))
    nm = os.path.join(ROOT, "tools/node/node_modules/three")
    shutil.copy(os.path.join(nm, "build/three.module.min.js"), os.path.join(OUT, "assets/three.module.min.js"))
    shutil.copy(os.path.join(nm, "examples/jsm/controls/OrbitControls.js"), os.path.join(OUT, "assets/OrbitControls.js"))
    shutil.rmtree(os.path.join(OUT, "viz"), ignore_errors=True)
    os.makedirs(os.path.join(OUT, "viz"), exist_ok=True)
    for fn in ["runtime.js", "boot.js"] + [m_["id"] + ".js" for m_ in VIZ.values()]:
        shutil.copy(os.path.join(ROOT, "viz", fn), os.path.join(OUT, "viz", fn))
    os.makedirs(os.path.join(OUT, "data"), exist_ok=True)
    json.dump([dict(AREAS[c], page=PAGES.get(c), mathlib=COV["areas"][c]) for c in sorted(AREAS)], open(os.path.join(OUT, "data/areas.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    json.dump(COV, open(os.path.join(OUT, "data/coverage.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    json.dump(ENVS, open(os.path.join(OUT, "data/environments.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
    open(os.path.join(OUT, "CNAME"), "w").write("math.renaissancelabs.eu\n")
    open(os.path.join(OUT, "robots.txt"), "w").write("User-agent: *\nAllow: /\nSitemap: %s/sitemap.xml\n" % SITE)
    open(os.path.join(OUT, ".nojekyll"), "w").write("")
    today = date.today().isoformat()
    open(os.path.join(OUT, "sitemap.xml"), "w").write('<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n%s\n</urlset>\n' % "\n".join("<url><loc>%s</loc><lastmod>%s</lastmod></url>" % (u, today) for u in sorted(SITEMAP)))
    open(os.path.join(OUT, "llms.txt"), "w").write(
        "# Renaissance Labs Mathematics\n\n> A map of all 63 areas of mathematics (MSC2020) with Lean/Mathlib formalization coverage, and Lean environments for training and evaluating proving.\n\n## Data\n- %s/data/areas.json\n- %s/data/coverage.json\n- %s/data/environments.json\n\n## Pages\n%s\n" % (SITE, SITE, SITE, "\n".join("- %s: %s" % (AREAS[c]["name"], "%s/area/%s/" % (SITE, c)) for c in sorted(AREAS))))
    print("built %d pages, %d formulas, %d areas with pages, %d environments" % (len(PAGES_OUT), len(MATH_JOBS), len(PAGES), len(ENVS)))

if __name__ == "__main__":
    main()
