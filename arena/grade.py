#!/usr/bin/env python3
"""Grade a Lean submission against a task. Standard library only.

  python3 grade.py --spec spec.json --solution Solution.lean --out <dir>

`spec.json` holds the hidden reference file, the target theorem names and their weights (see
arena/core.py). The reward is the weighted share of targets that are proved: stated exactly as
asked, with no `sorry`, depending only on propext, Classical.choice and Quot.sound, and passing a
second kernel check by `leanchecker`. A submission that does not compile scores 0.

The Lean project (toolchain + Mathlib) is found through $ARENA_LEAN, default: ../lean next to this
file, then /opt/arena/lean.
"""
import argparse, json, os, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
TIMEOUT = int(os.environ.get("ARENA_TIMEOUT", "600"))

def project():
    for p in (os.environ.get("ARENA_LEAN"), os.path.join(HERE, "..", "lean"), "/opt/arena/lean"):
        if p and os.path.exists(os.path.join(p, "lean-toolchain")): return os.path.abspath(p)
    raise SystemExit("Lean project not found; set ARENA_LEAN")

_lp = {}
def lean_path(proj):
    if proj not in _lp:
        cache = os.path.join(proj, ".lake", "lean_path.txt")
        if os.path.exists(cache): _lp[proj] = open(cache).read().strip()
        else:
            _lp[proj] = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=proj, capture_output=True, text=True, check=True).stdout.strip()
            try: open(cache, "w").write(_lp[proj])
            except OSError: pass
    return _lp[proj]

class Slot:
    """Optional machine-wide cap on concurrent Lean processes: ARENA_SLOTS=n, ARENA_LOCKDIR=dir."""
    def __enter__(self):
        self.path = None
        n = int(os.environ.get("ARENA_SLOTS", "0"))
        if not n: return self
        d = os.environ.get("ARENA_LOCKDIR", os.path.join(tempfile.gettempdir(), "arena-locks")); os.makedirs(d, exist_ok=True)
        while True:
            for i in range(n):
                p = os.path.join(d, "slot%d" % i)
                try:
                    os.mkdir(p); open(os.path.join(p, "pid"), "w").write(str(os.getpid())); self.path = p; return self
                except FileExistsError:
                    try:
                        pid = int(open(os.path.join(p, "pid")).read()); os.kill(pid, 0)
                    except (OSError, ValueError):
                        shutil.rmtree(p, ignore_errors=True)   # stale
            time.sleep(1)
    def __exit__(self, *a):
        if self.path: shutil.rmtree(self.path, ignore_errors=True)

def run(cmd, proj, extra_path=None, timeout=TIMEOUT):
    env = dict(os.environ); env["LEAN_PATH"] = lean_path(proj) + ((":" + extra_path) if extra_path else "")
    with Slot():
        try:
            r = subprocess.run(cmd, cwd=proj, env=env, capture_output=True, text=True, timeout=timeout)
            return r.returncode, (r.stdout + r.stderr)
        except subprocess.TimeoutExpired:
            return 124, "timed out after %d s" % timeout

def compile_lean(proj, src, work):
    """Compile work/<src>.lean to work/<src>.olean. Returns (ok, messages)."""
    olean = os.path.join(work, src + ".olean")
    if os.path.exists(olean): os.remove(olean)
    code, out = run(["lean", "--root=" + work, "-o", olean, os.path.join(work, src + ".lean")], proj, work)
    return code == 0 and os.path.exists(olean), out

def grade(spec, solution_text, keep=None):
    proj = project(); work = keep or tempfile.mkdtemp(prefix="arena-")
    os.makedirs(work, exist_ok=True)
    targets = spec["targets"]; total = float(sum(t["weight"] for t in targets))
    res = {"reward": 0.0, "stage": "", "targets": [], "log": ""}
    def fail(stage, log):
        res["stage"] = stage; res["log"] = log[-4000:]
        res["targets"] = [{"target": t["name"], "ok": False, "why": stage} for t in targets]
        return res
    try:
        open(os.path.join(work, "Reference.lean"), "w").write(spec["reference"])
        open(os.path.join(work, "Solution.lean"), "w").write(solution_text)
        ok, out = compile_lean(proj, "Reference", work)
        if not ok: return fail("the reference file did not compile (a fault in the task, not in the submission)", out)
        ok, out = compile_lean(proj, "Solution", work)
        if not ok: return fail("the submission does not compile", out)
        code, out = run(["leanchecker", "Solution"], proj, work)
        if code != 0: return fail("the submission fails the kernel re-check", out)
        sub = "Solution"; flags = []
        if spec.get("tests"):
            open(os.path.join(work, "Tests.lean"), "w").write(spec["tests"])
            ok, out = compile_lean(proj, "Tests", work)
            if not ok: return fail("the hidden tests do not pass", out)
            code, out = run(["leanchecker", "Tests"], proj, work)
            if code != 0: return fail("the tests fail the kernel re-check", out)
            sub = "Tests"; flags = ["--native"]
        if spec.get("free"): flags += ["--free", ",".join(spec["free"])]
        verify = os.path.join(HERE, "Verify.lean")
        if not os.path.exists(verify): verify = os.path.join(proj, "verifier", "Verify.lean")
        code, out = run(["lean", "--run", verify] + flags + ["Reference", sub] + [t["name"] for t in targets], proj, work)
        got = {}
        for line in out.splitlines():
            if line.startswith("{"):
                try: j = json.loads(line); got[j["target"]] = j
                except ValueError: pass
        if code != 0 or len(got) != len(targets): return fail("the verifier did not finish", out)
        res["targets"] = [got[t["name"]] for t in targets]
        res["reward"] = round(sum(t["weight"] for t in targets if got[t["name"]]["ok"]) / total, 4)
        res["stage"] = "graded"
        return res
    finally:
        if not keep: shutil.rmtree(work, ignore_errors=True)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--spec", required=True); ap.add_argument("--solution", required=True); ap.add_argument("--out", default=None)
    a = ap.parse_args()
    spec = json.load(open(a.spec, encoding="utf-8"))
    try: text = open(a.solution, encoding="utf-8").read()
    except OSError: text = None
    res = grade(spec, text) if text is not None else {"reward": 0.0, "stage": "no Solution.lean found", "targets": [], "log": ""}
    print(json.dumps(res, indent=1, ensure_ascii=False))
    if a.out:
        os.makedirs(a.out, exist_ok=True)
        open(os.path.join(a.out, "reward.txt"), "w").write("%g\n" % res["reward"])
        json.dump(res, open(os.path.join(a.out, "result.json"), "w"), indent=1, ensure_ascii=False)
