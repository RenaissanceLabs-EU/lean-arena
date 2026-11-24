# Authoring a Lean environment

An environment is a generator of Lean tasks in one area of mathematics (an MSC2020 area). Each task gives an agent a `Solution.lean` containing statements with `sorry`; the agent replaces the `sorry`s; a hidden grader (`arena/grade.py` + `lean/verifier/Verify.lean`) gives a reward in [0, 1]. Read `envs/finite_sums/` (kind `prove`) and `envs/definitions/` (kind `define`) first and copy their shape. `arena/core.py` is the task model.

## Files in `envs/<folder>/` (folder name uses underscores)

- `__init__.py` (empty), `env.toml` (keys as in the two examples: `name` kebab-case, `title`, `msc` two-digit area, `kind`, `summary` one sentence at most 160 characters, `skill` a short phrase, `good_for` list, `families` list).
- `gen.py`: `generate(seed, difficulty, family=None) -> arena.core.Task`; `FAMILIES` list; default family `sorted(FAMILIES)[seed % len(FAMILIES)]`; difficulty 1, 2 or 3; randomness only from `rng_for(ENV + "/" + family, seed, difficulty)`. Python 3.9, standard library only. 3 to 5 families per environment.

## Rules

1. **Every statement must be true and the reference proof must compile.** The reference proofs are real Lean proofs in `Theorem.proof` (or reference definitions in `Task.solution`). Never ship a family whose proof is only checked for some seeds: the self-test compiles 30 tasks per run; run it with several sizes.
2. **Two code paths for anything numeric.** If a statement depends on computed values (a constant, a bound, a count), compute them in Python and assert them against an independent Python check before returning, as `finite_sums` does with exact fractions.
3. **Exact statements, no vacuity.** No hypotheses that are contradictory, no statements trivially true by `rfl`/`simp`/`decide` at difficulty 2 and 3 (difficulty 1 may need one real idea). Avoid statements a single `omega`, `norm_num`, `simp` or `decide` call closes in every family: each family should need a genuine proof idea at difficulty 2 and above (induction, case analysis, a Mathlib lemma search, a construction). Check by trying `by decide`, `by simp`, `by omega`, `by norm_num`, `by aesop`, `by nlinarith` yourself on a sample and reporting which tasks fall to one-liners, then redesign those.
4. **The instruction states the problem in words** (`informal`, Markdown with maths in `\( \)` and `\[ \]`). Give each theorem a one-line `informal` doc comment. The statement is also in `Solution.lean`.
5. **Variety.** Parameters vary enough that at least 90 percent of tasks differ across 10 seeds per difficulty (the self-test checks this). Difficulty 1: one idea. 2: two ideas or a longer proof. 3: a multi-step argument or a cross-lemma combination. Multi-theorem tasks (a lemma plus a main theorem that uses it) are welcome; use `weight` to weight the main theorem.
6. **Mathlib names:** this project is on Lean 4.29.1 with the Mathlib in `lean/.lake/packages/mathlib`. Use `grep -rn` there to confirm names before using them. `∑ i ∈ s, f i` is current syntax. Hidden state: do not leak reference proofs into the instruction or start file.
7. **Prefer `prove` tasks.** A `define` task is good only when the hidden `native_decide` test makes a meaningful check; follow `envs/definitions/`.
8. American English, short plain sentences, no em dashes, no emoji.

## Self-test

```bash
ARENA_SLOTS=3 python3 tools/selftest.py <folder> 10 --e2e 2
```

It checks determinism, 90 percent distinct tasks, that every reference solution compiles (batched in one Lean run), and that the real grader gives the reference solution 1.0 and the untouched start file 0.0. **It must print `0 failures`.** `ARENA_SLOTS=3` is mandatory: it caps concurrent Lean processes machine-wide so memory is not exhausted. Never run more than one selftest at once yourself, never run `lake build`, `lake update` or anything that rebuilds Mathlib, and do not edit anything under `lean/` or `arena/`. A compile of the batch takes a few minutes; use `timeout` of 600000 ms and run it in the background if needed.

Also write `tests/test_<folder>.py` (plain asserts): for each family, at least two hand-derived facts about the generator (for example the exact statement produced for a fixed seed, or a Python-side value worked by hand) so a regression in the generator is caught.

## Report

Report only: families, which Mathlib lemmas the proofs rely on, anything you were unsure about, the one-liner findings from rule 3, and the self-test output lines.
