#!/usr/bin/env python3
"""Generate the social preview images (1200 x 630 JPEG) into docs/assets/og/.

  python3 tools/make_og.py            # all pages
  python3 tools/make_og.py home a11   # only these names

Names: home, frontier, checking, environments, about, a<code> (area pages), e<slug> (environments).
Each image is HTML rendered by headless Chrome (tools/render_og.mjs). The map graphic is the real
data: 63 tiles grouped by family, lit by how much of the area is in Mathlib.
"""
import html, json, math, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools")); sys.path.insert(0, ROOT)
import build as B
e = html.escape
OUT = os.path.join(ROOT, "docs", "assets", "og")
FONTS = os.path.join(ROOT, "docs", "assets", "fonts")

HUES = ["#a39c90", "#d09558", "#cf7f68", "#b784af", "#8399c9", "#74a893", "#e0b657", "#a0af5c"]   # dark-theme family colours
GOLD = "#e0b657"

CSS = """
@font-face{font-family:'Fraunces';font-style:normal;font-weight:100 900;src:url('file://%(f)s/fraunces-latin-opsz-normal.woff2') format('woff2')}
@font-face{font-family:'Fraunces';font-style:italic;font-weight:100 900;src:url('file://%(f)s/fraunces-latin-opsz-italic.woff2') format('woff2')}
*{box-sizing:border-box;margin:0}
html,body{width:1200px;height:630px;overflow:hidden}
body{position:relative;background:radial-gradient(70%% 90%% at 82%% 8%%,rgba(120,84,40,.38),transparent 62%%),radial-gradient(60%% 80%% at 8%% 100%%,rgba(40,60,130,.35),transparent 60%%),linear-gradient(135deg,#070a1c,#0d1330 55%%,#141a38);
 color:#f3eee3;font-family:-apple-system,'Helvetica Neue',Arial,sans-serif}
.brand{position:absolute;left:72px;top:60px;font:600 20px/1 -apple-system,Arial,sans-serif;letter-spacing:.2em;text-transform:uppercase;color:%(gold)s}
.brand i{font:italic 400 28px/1 'Fraunces',Georgia,serif;letter-spacing:0;text-transform:none;margin-left:10px;color:#f3d79b}
.serif{font-family:'Fraunces',Georgia,serif;font-weight:400;letter-spacing:-.02em}
.h1{position:absolute;left:72px;top:148px;width:650px;font-size:84px;line-height:1.0}
.h1 em{font-style:italic;color:%(gold)s}
.sub{position:absolute;left:72px;bottom:62px;width:600px;font-size:25px;line-height:1.45;color:#cfc8b8}
.url{position:absolute;left:72px;bottom:28px;font:500 16px/1 ui-monospace,Menlo,monospace;color:#8f89a0;letter-spacing:.04em}
svg.lor{position:absolute;inset:0;width:1200px;height:630px}
.map{position:absolute;right:64px;top:67px}
.t{position:absolute;width:48px;height:48px;border-radius:8px}
.glow{box-shadow:0 0 30px 6px var(--c)}
""" % {"f": FONTS, "gold": GOLD}

def lorenz_path():
    """A real Lorenz trajectory (sigma 10, rho 28, beta 8/3), projected onto the page as a thin glowing curve."""
    s, r, b = 10.0, 28.0, 8.0 / 3.0
    x, y, z = 1.0, 1.0, 1.0; dt = 0.006; pts = []
    f = lambda x, y, z: (s * (y - x), x * (r - z) - y, x * y - b * z)
    for i in range(9000):
        k1 = f(x, y, z); k2 = f(x + dt / 2 * k1[0], y + dt / 2 * k1[1], z + dt / 2 * k1[2])
        k3 = f(x + dt / 2 * k2[0], y + dt / 2 * k2[1], z + dt / 2 * k2[2]); k4 = f(x + dt * k3[0], y + dt * k3[1], z + dt * k3[2])
        x += dt / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]); y += dt / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]); z += dt / 6 * (k1[2] + 2 * k2[2] + 2 * k3[2] + k4[2])
        if i > 300 and i % 3 == 0: pts.append((x, z))
    xs = [p[0] for p in pts]; zs = [p[1] for p in pts]
    # fit to the right 55% of the page, slightly rotated for a livelier shape
    w, h = 820, 520; x0, x1, z0, z1 = min(xs), max(xs), min(zs), max(zs)
    out = []
    for (px, pz) in pts:
        u = (px - x0) / (x1 - x0); v = (pz - z0) / (z1 - z0)
        out.append((560 + u * w * 0.76 + v * 30, 592 - v * h * 0.98))
    return "M" + " L".join("%.1f %.1f" % p for p in out)

LORENZ = lorenz_path()

def lorenz_svg(opacity=0.5):
    return ('<svg class="lor" viewBox="0 0 1200 630"><defs><filter id="g"><feGaussianBlur stdDeviation="3.2"/></filter></defs>'
            '<path d="%s" fill="none" stroke="%s" stroke-width="2.6" opacity="%.2f" filter="url(#g)"/>'
            '<path d="%s" fill="none" stroke="#f3d79b" stroke-width="0.9" opacity="%.2f"/></svg>') % (LORENZ, GOLD, opacity * 0.9, LORENZ, opacity)

ORDER = [c for _, _, cs in B.GROUPS for c in cs]      # 63 areas, family by family

def mix(hue, a, bg=(15, 20, 49)):
    h = tuple(int(hue[i:i + 2], 16) for i in (1, 3, 5))
    return "#%02x%02x%02x" % tuple(int(bg[k] + (h[k] - bg[k]) * a) for k in range(3))

def tile_map(highlight=None):
    cols, rows, size, gap = 7, 9, 48, 8
    parts = []; mx = math.log10(max(B.cov(c) for c in ORDER) + 1)
    for i, c in enumerate(ORDER):
        col, row = i % cols, i // cols
        x, y = col * (size + gap), row * (size + gap)
        hue = HUES[B.GROUP_OF[c][0]]; n = B.cov(c); lvl = 0 if n == 0 else math.log10(n + 1) / mx
        if highlight and c != highlight:
            style = "background:%s" % mix(hue, 0.14 + 0.22 * lvl) if n else "border:1.5px dashed rgba(243,238,227,.14)"
        elif highlight:
            style = "background:%s;--c:%s;transform:scale(1.28);z-index:3" % (hue, hue)
            parts.append('<div class="t glow" style="left:%dpx;top:%dpx;%s"></div>' % (x, y, style)); continue
        elif n == 0: style = "border:1.5px dashed rgba(243,238,227,.28)"
        else: style = "background:%s" % mix(hue, 0.34 + 0.66 * lvl)
        parts.append('<div class="t" style="left:%dpx;top:%dpx;%s"></div>' % (x, y, style))
    return '<div class="map" style="width:%dpx;height:%dpx">%s</div>' % (cols * (size + gap), rows * (size + gap), "".join(parts))

def page(inner): return '<!doctype html><meta charset="utf-8"><style>%s</style><body>%s</body>' % (CSS, inner)

def home():
    n = B.COV["mathlib_theorems"]
    return page(f'''{lorenz_svg(.34)}{tile_map()}
<div class="brand">Renaissance Labs<i>Mathematics</i></div>
<h1 class="h1 serif">All of mathematics, <em>mapped</em> and <em>formalized.</em></h1>
<p class="sub">Every field, what Lean already knows of it, and where intelligence can learn to prove the rest.</p>
<div class="url">math.renaissancelabs.eu</div>''')

def area(c):
    a = B.AREAS[c]; p = B.PAGES.get(c); gi = B.GROUP_OF[c][0]; hue = HUES[gi]; n = B.cov(c)
    title = B.area_label(c) if p else a["name"]
    hook = re_math(p["hook"]) if p else ""
    stat = ("%s theorems in Mathlib &middot; ranked %d of 63" % (B.fmt(n), B.RANK[c])) if n else "Almost nothing in Mathlib yet"
    size = 84 if len(title) <= 18 else 68 if len(title) <= 26 else 56
    viz = '<span style="margin-left:18px;color:#cfc8b8">&#9679; interactive figure</span>' if c in B.VIZ else ""
    return page(f'''{lorenz_svg(.18)}{tile_map(c)}
<div class="brand">Renaissance Labs<i>Mathematics</i></div>
<div style="position:absolute;left:72px;top:140px;width:640px">
<div style="font:500 19px ui-monospace,Menlo,monospace;color:{hue};letter-spacing:.06em">MSC {c} &middot; {e(B.GROUP_OF[c][2].upper())}</div>
<h1 class="serif" style="margin-top:18px;font-size:{size}px;line-height:1.02">{e(title)}</h1>
<p class="serif" style="margin-top:26px;font-style:italic;font-size:29px;line-height:1.38;color:#d9d2c2">{e(hook)}</p></div>
<p class="sub" style="font-size:20px;color:{hue}">{stat}{viz}</p>
<div class="url">math.renaissancelabs.eu/area/{c}</div>''')

def re_math(s):
    import re
    s = re.sub(r"\\\((.*?)\\\)", lambda m: m.group(1).replace("\\", ""), s)
    return s

def env(m):
    import importlib
    gen = importlib.import_module("envs.%s.gen" % m["folder"]); t = gen.generate(1, 2)
    code = t.start_file().replace("import Mathlib\n", "").strip()
    lines = [l for l in code.split("\n") if not l.startswith("/--")][:6]; code = "\n".join(lines)
    gi = B.GROUP_OF[m["msc"]][0]; hue = HUES[gi]
    return page(f'''{lorenz_svg(.16)}
<div class="brand">Renaissance Labs<i>Mathematics</i></div>
<div style="position:absolute;left:72px;top:140px;width:600px">
<div style="font:500 19px ui-monospace,Menlo,monospace;color:{hue};letter-spacing:.06em">LEAN ENVIRONMENT &middot; MSC {m["msc"]}</div>
<h1 class="serif" style="margin-top:18px;font-size:64px;line-height:1.04">{e(m["title"])}</h1></div>
<p class="sub" style="width:560px;font-size:23px;bottom:84px">{e(m["summary"])}</p>
<p class="sub" style="bottom:50px;font-size:18px;color:{hue}">{B.TRAIN + B.EVAL} tasks &middot; reward from the Lean kernel</p>
<div class="url">math.renaissancelabs.eu/env/{m["slug"]}</div>
<div style="position:absolute;right:64px;top:150px;width:440px;padding:26px 28px;border-radius:16px;background:rgba(8,10,26,.78);border:1px solid rgba(243,238,227,.14);box-shadow:0 24px 60px rgba(0,0,0,.45)">
<pre style="font:500 18px/1.6 ui-monospace,Menlo,monospace;color:#e9e2d2;white-space:pre-wrap;word-break:break-word">{e(code)}</pre></div>''')

def generic(label, title, sub, big=None):
    bigs = "".join('<div style="margin-right:44px"><div class="serif" style="font-size:78px;line-height:1">%s</div><div style="font-size:17px;color:#cfc8b8;margin-top:8px;max-width:210px">%s</div></div>' % (a, b) for a, b in (big or []))
    return page(f'''{lorenz_svg(.26)}
<div class="brand">Renaissance Labs<i>Mathematics</i></div>
<div style="position:absolute;left:72px;top:140px;width:780px">
<div style="font:500 19px ui-monospace,Menlo,monospace;color:{GOLD};letter-spacing:.06em">{e(label.upper())}</div>
<h1 class="serif" style="margin-top:18px;font-size:76px;line-height:1.02">{title}</h1></div>
<div style="position:absolute;left:72px;bottom:120px;display:flex">{bigs}</div>
<p class="sub" style="width:700px;font-size:23px">{e(sub)}</p><div class="url">math.renaissancelabs.eu</div>''')

def jobs():
    j = {"home": home()}
    h_ok = sum(1 for x in B.COV["hundred"] if x["formalized"]); th = B.COV["thousand"]
    j["frontier"] = generic("Formalization frontier", "What Lean knows, and what it does not <em>yet</em>", "Three Lean-community lists show how much of mathematics is formalized.",
                            [("%d / 100" % h_ok, "famous theorems formalized"), ("%d / %s" % (th["in_mathlib"], B.fmt(th["listed"])), "of the 1000+ list in Mathlib")])
    j["checking"] = generic("Trust", "How a proof is <em>checked</em>", "What counts as proved, and the cheating attempts the checker was tested against.")
    j["environments"] = generic("Lean environments", "Where intelligence <em>practices</em> mathematics", "Generated Lean tasks with a reward from the Lean kernel.", [(str(len(B.ENVS)), "environments"), (B.fmt(len(B.ENVS) * (B.TRAIN + B.EVAL)), "checked tasks")])
    j["about"] = generic("About", "A map, and a place to <em>practice</em>", "How the mathematics map and the Lean environments are made.")
    for c in B.AREAS: j["a" + c] = area(c)
    for m in B.ENVS: j["e" + m["slug"]] = env(m)
    return j

def main():
    only = sys.argv[1:]; allj = jobs()
    sel = {k: v for k, v in allj.items() if not only or k in only}
    os.makedirs(OUT, exist_ok=True)
    spec = [{"name": k, "html": v} for k, v in sel.items()]
    tmp = os.path.join(ROOT, ".og_jobs.json"); json.dump(spec, open(tmp, "w"))
    r = subprocess.run(["node", os.path.join(ROOT, "tools", "render_og.mjs"), tmp, OUT], capture_output=True, text=True)
    os.remove(tmp); print(r.stdout.strip());
    if r.returncode: print(r.stderr[-800:]); sys.exit(1)

if __name__ == "__main__":
    main()
