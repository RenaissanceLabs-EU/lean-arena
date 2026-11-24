#!/usr/bin/env python3
"""Export every environment as Harbor task folders under tasks/<env>/<task_id>/.

  python3 tools/export.py              # all environments
  python3 tools/export.py definitions  # one

Each task folder:
  instruction.md                what the agent is asked to do
  task.toml                     metadata and limits
  environment/Dockerfile        FROM lean-arena (see docker/Dockerfile), copies Solution.lean to /app
  environment/workdir/Solution.lean   the start file
  solution/solve.sh, Solution.lean    reference solution (never shown to the agent)
  tests/test.sh, spec.json, grade.py  hidden grader; writes /logs/verifier/reward.txt
84 train and 24 held-out eval tasks per environment; eval seeds start at 10000.
"""
import importlib, json, os, shutil, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
TRAIN, EVAL, EVAL_BASE = 84, 24, 10000

def read_toml(path):
    out = {}
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line: continue
        k, v = line.split("=", 1); out[k.strip()] = json.loads(v.strip())
    return out

def plan(families):
    f = len(families)
    for split, n, base in (("train", TRAIN, 0), ("eval", EVAL, EVAL_BASE)):
        for i in range(n):
            yield split, base + i, sorted(families)[i % f], 1 + (i // f) % 3

def write(path, text, mode=None):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w", encoding="utf-8").write(text)
    if mode: os.chmod(path, mode)

TEST = '#!/bin/bash\nmkdir -p /logs/verifier\npython3 /tests/grade.py --spec /tests/spec.json --solution /app/Solution.lean --out /logs/verifier || echo 0 > /logs/verifier/reward.txt\n'
SOLVE = "#!/bin/bash\nset -e\ncp /solution/Solution.lean /app/Solution.lean\n"

def main():
    only = sys.argv[1:]; manifest = []
    grade_src = open(os.path.join(ROOT, "arena", "grade.py"), encoding="utf-8").read()
    for d in sorted(os.listdir(os.path.join(ROOT, "envs"))):
        tp = os.path.join(ROOT, "envs", d, "env.toml")
        if not os.path.exists(tp) or (only and d not in only): continue
        meta = read_toml(tp); gen = importlib.import_module("envs.%s.gen" % d)
        out = os.path.join(ROOT, "tasks", meta["name"]); shutil.rmtree(out, ignore_errors=True)
        for split, seed, family, difficulty in plan(meta["families"]):
            t = gen.generate(seed, difficulty, family)
            tid = "%s-%s-d%d-%s%04d" % (meta["name"], family, difficulty, "e" if split == "eval" else "t", seed % EVAL_BASE)
            td = os.path.join(out, tid)
            write(os.path.join(td, "instruction.md"), t.instruction())
            write(os.path.join(td, "task.toml"), "\n".join([
                'version = "1.0"', "", "[metadata]", 'author_name = "Renaissance Labs"', 'author_email = "unknown"',
                'difficulty = "%s"' % {1: "easy", 2: "medium", 3: "hard"}[difficulty], 'category = "%s"' % meta["name"],
                "tags = %s" % json.dumps([meta["name"], family, "msc-" + meta["msc"], split, "lean4"]),
                'msc = "%s"' % meta["msc"], 'family = "%s"' % family, 'split = "%s"' % split, "seed = %d" % seed, "",
                "[verifier]", "timeout_sec = 900.0", "", "[agent]", "timeout_sec = 1800.0", "",
                "[environment]", "build_timeout_sec = 1800.0", "cpus = 2", "memory_mb = 6144", "storage_mb = 10240", "allow_internet = false", ""]))
            write(os.path.join(td, "environment", "Dockerfile"), "FROM lean-arena\nWORKDIR /app\nCOPY workdir/ /app/\n")
            write(os.path.join(td, "environment", "workdir", "Solution.lean"), t.start_file())
            write(os.path.join(td, "solution", "solve.sh"), SOLVE, 0o755)
            write(os.path.join(td, "solution", "Solution.lean"), t.reference_solution())
            write(os.path.join(td, "tests", "test.sh"), TEST, 0o755)
            write(os.path.join(td, "tests", "spec.json"), json.dumps(t.spec(), indent=1, ensure_ascii=False) + "\n")
            write(os.path.join(td, "tests", "grade.py"), grade_src)
            shutil.copy(os.path.join(ROOT, "lean", "verifier", "Verify.lean"), os.path.join(td, "tests", "Verify.lean"))
            manifest.append({"id": tid, "env": meta["name"], "msc": meta["msc"], "family": family, "difficulty": difficulty, "split": split, "seed": seed,
                             "kind": t.kind, "path": "tasks/%s/%s" % (meta["name"], tid)})
        print("%-26s %d tasks" % (meta["name"], TRAIN + EVAL))
    if not only:
        with open(os.path.join(ROOT, "tasks.jsonl"), "w", encoding="utf-8") as f:
            for m in manifest: f.write(json.dumps(m, ensure_ascii=False) + "\n")
    print(len(manifest), "tasks")

if __name__ == "__main__":
    main()
