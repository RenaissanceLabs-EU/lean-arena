#!/usr/bin/env python3
"""Generate one task into a folder: instruction.md, Solution.lean (the start file), spec.json (hidden, for the grader).

  python3 tools/make_task.py <env_folder> --seed 7 --difficulty 2 [--family name] --out /tmp/task
"""
import argparse, importlib, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
ap = argparse.ArgumentParser()
ap.add_argument("env"); ap.add_argument("--seed", type=int, default=0); ap.add_argument("--difficulty", type=int, default=1)
ap.add_argument("--family", default=None); ap.add_argument("--out", required=True)
a = ap.parse_args()
t = importlib.import_module("envs.%s.gen" % a.env).generate(a.seed, a.difficulty, a.family)
os.makedirs(a.out, exist_ok=True)
open(os.path.join(a.out, "instruction.md"), "w", encoding="utf-8").write(t.instruction())
open(os.path.join(a.out, "Solution.lean"), "w", encoding="utf-8").write(t.start_file())
json.dump(t.spec(), open(os.path.join(a.out, "spec.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)
print("wrote", a.out, "(%s, %s, difficulty %d)" % (t.env, t.family, t.difficulty))
