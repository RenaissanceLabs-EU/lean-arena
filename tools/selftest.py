#!/usr/bin/env python3
"""Self-test for one environment.

  python3 tools/selftest.py <env_folder> [n_per_difficulty=10] [--e2e 2]

For n seeds at each difficulty (3n tasks):
  1. generation is deterministic;
  2. every reference solution compiles, with every hidden test, in one batched Lean run;
  3. statements are not repeated across seeds more than a little;
then, for --e2e sampled tasks, the real grader must give the reference solution 1.0 and the
untouched start file 0.0.
"""
import importlib, json, os, re, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from arena import grade as G

def batch_source(tasks):
    """All reference solutions in one file, one namespace each. Returns (text, line -> task index)."""
    lines = ["import Mathlib", ""]; owner = {}
    for i, t in enumerate(tasks):
        body = t.reference_solution().split("\n", 1)[1]
        if t.tests:
            for x in t.tests: body += "\ntheorem %s %s := %s\n" % (x.name, x.statement.strip(), x.proof)
        chunk = ["namespace T%d" % i] + body.split("\n") + ["end T%d" % i, ""]
        for k in range(len(chunk)): owner[len(lines) + k + 1] = i
        lines += chunk
    return "\n".join(lines) + "\n", owner

def compile_batch(tasks, label):
    proj = G.project(); work = tempfile.mkdtemp(prefix="arena-batch-")
    text, owner = batch_source(tasks)
    open(os.path.join(work, "Batch.lean"), "w").write(text)
    code, out = G.run(["lean", "--root=" + work, os.path.join(work, "Batch.lean")], proj, timeout=3000)
    bad = {}
    for m in re.finditer(r"Batch\.lean:(\d+):\d+: (error|warning): (.*(?:\n(?!\S*Batch\.lean:\d+).*)*)", out):
        line, kind, msg = int(m.group(1)), m.group(2), m.group(3)
        if kind == "error" or "sorry" in msg: bad.setdefault(owner.get(line, -1), []).append("%s: %s" % (kind, msg.strip()[:400]))
    if code != 0 and not bad: bad[-1] = [out[-800:]]
    return bad, work

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    folder = args[0]; n = int(args[1]) if len(args) > 1 else 10
    e2e = int(sys.argv[sys.argv.index("--e2e") + 1]) if "--e2e" in sys.argv else 2
    gen = importlib.import_module("envs.%s.gen" % folder)
    fams = sorted(gen.FAMILIES); tasks = []; fails = 0
    for d in (1, 2, 3):
        for s in range(n):
            for f in ([None] if n >= len(fams) else [None]):
                t = gen.generate(s, d, f); t2 = gen.generate(s, d, f)
                if t.reference_solution() != t2.reference_solution() or t.instruction() != t2.instruction():
                    print("NOT DETERMINISTIC seed %d d%d" % (s, d)); fails += 1
                assert t.family in fams, t.family
                tasks.append(t)
    keys = [t.start_file() + t.informal for t in tasks]
    uniq = len(set(keys)) / float(len(keys))
    print("%d tasks, %d families seen, %.0f%% distinct tasks" % (len(tasks), len({t.family for t in tasks}), 100 * uniq))
    if uniq < 0.9: print("TOO MANY REPEATS"); fails += 1
    for lo in range(0, len(tasks), 30):
        part = tasks[lo:lo + 30]
        bad, work = compile_batch(part, folder)
        for i, msgs in sorted(bad.items()):
            fails += 1
            t = part[i] if i >= 0 else None
            print("REFERENCE FAILS %s" % (("%s seed %d d%d" % (t.family, t.seed, t.difficulty)) if t else "(batch)"))
            for m in msgs[:3]: print("   ", m.replace("\n", "\n    "))
            if t: print("    --- statement:", (t.theorems[0].statement if t.theorems else t.solution)[:300].replace("\n", " "))
    print("batched compile of reference solutions: %s" % ("ok" if not fails else "FAILURES"))
    step = max(1, len(tasks) // max(e2e, 1))
    for t in tasks[::step][:e2e]:
        r1 = G.grade(t.spec(), t.reference_solution()); r0 = G.grade(t.spec(), t.start_file())
        ok = r1["reward"] == 1.0 and r0["reward"] == 0.0
        print("end to end %s seed %d d%d: reference %.2f, start file %.2f %s" % (t.family, t.seed, t.difficulty, r1["reward"], r0["reward"], "ok" if ok else "FAIL"))
        if not ok: fails += 1; print("   ", r1["stage"], r1["log"][-600:], "|", r0["stage"])
    print("SELFTEST %s: %d failures" % (folder, fails))
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
