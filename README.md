# Renaissance Labs Mathematics

Source for https://math.renaissancelabs.eu: a map of all 63 areas of mathematics (MSC2020) with Lean/Mathlib formalization coverage, and Lean environments in which a model proves theorems or writes definitions, with a reward from the Lean kernel.

```
docs/            the built site (static HTML, served by GitHub Pages)
data/            msc.json (MSC2020), areas/*.json (one page per area), coverage.json (measured from Mathlib)
envs/            environments: env.toml + gen.py per folder; contract in AUTHORING.md
arena/           task model (core.py) and the grader (grade.py)
lean/            Lean project (Mathlib) and verifier/Verify.lean
tools/           build.py (site), selftest.py, make_task.py, export.py (Harbor), mathlib_coverage.py
docker/          image with Lean, Mathlib cache and the grader
```

## Commands

```bash
python3 tools/mathlib_coverage.py            # re-measure Mathlib (after bumping lean/lake-manifest.json)
python3 tools/build.py                       # rebuild docs/ (needs node: cd tools/node && npm install katex@0.16.11)
ARENA_SLOTS=3 python3 tools/selftest.py <env_folder> 10 --e2e 2   # must print 0 failures
python3 tools/export.py                      # Harbor task folders in tasks/
```

First-time Lean setup: `cd lean && lake exe cache get` (downloads the prebuilt Mathlib, about 5 GB unpacked).

## How checking works

`arena/grade.py` compiles the submission, re-checks it with `leanchecker`, then runs `lean/verifier/Verify.lean`, which loads the hidden reference and the submission into separate environments, compares kernel terms, and allows only `propext`, `Classical.choice` and `Quot.sound`. Tested against sorry, `native_decide`, a changed definition, a weaker statement, a kernel-skipping `addDecl`, and a user axiom.

Code MIT, data and content CC BY 4.0.
