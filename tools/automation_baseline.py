#!/usr/bin/env python3
"""Share of tasks that one automation call closes, per environment and difficulty.

  ARENA_SLOTS=3 python3 tools/automation_baseline.py [seeds_per_difficulty=8]

Each theorem's proof is replaced by `first | grind | aesop | simp | omega | norm_num | nlinarith | decide`.
A task counts as closed only if every theorem in it is closed. Writes data/baseline.json.
This is a floor on difficulty: a model that merely learns to call these tactics scores this much.
"""
import importlib, json, os, re, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from arena import grade as G
AUTO = "by\n  first | grind | aesop | (simp; done) | omega | norm_num | nlinarith [sq_nonneg (1:ℝ)] | decide"

def read_toml(path):
    out = {}
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1); out[k.strip()] = json.loads(v.strip())
    return out

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    result = {}
    for d in sorted(os.listdir(os.path.join(ROOT, "envs"))):
        tp = os.path.join(ROOT, "envs", d, "env.toml")
        if not os.path.exists(tp): continue
        meta = read_toml(tp)
        if meta["kind"] != "prove": continue
        gen = importlib.import_module("envs.%s.gen" % d)
        tasks = [(diff, gen.generate(s, diff)) for diff in (1, 2, 3) for s in range(n)]
        lines = ["import Mathlib", ""]; owner = {}
        for i, (diff, t) in enumerate(tasks):
            chunk = ["namespace T%d" % i]
            if t.preamble.strip(): chunk += t.preamble.strip().split("\n")
            for th in t.theorems: chunk += ("theorem %s %s := %s" % (th.name, th.statement.strip(), AUTO)).split("\n")
            chunk += ["end T%d" % i, ""]
            for k in range(len(chunk)): owner[len(lines) + k + 1] = i
            lines += chunk
        proj = G.project(); work = tempfile.mkdtemp(prefix="arena-auto-")
        open(os.path.join(work, "B.lean"), "w").write("\n".join(lines) + "\n")
        code, out = G.run(["lean", "--root=" + work, os.path.join(work, "B.lean")], proj, timeout=3000)
        failed = set()
        for m in re.finditer(r"B\.lean:(\d+):\d+: error", out): failed.add(owner.get(int(m.group(1)), -1))
        per = {1: [0, 0], 2: [0, 0], 3: [0, 0]}
        for i, (diff, t) in enumerate(tasks):
            per[diff][1] += 1; per[diff][0] += (i not in failed)
        result[meta["name"]] = {str(k): {"closed": v[0], "tasks": v[1]} for k, v in per.items()}
        print("%-26s" % meta["name"], "  ".join("d%d %d/%d" % (k, v[0], v[1]) for k, v in per.items()), flush=True)
    json.dump(result, open(os.path.join(ROOT, "data", "baseline.json"), "w"), indent=1)

if __name__ == "__main__":
    main()
