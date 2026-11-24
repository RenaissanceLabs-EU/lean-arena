"""Task model for the Lean environments. Python 3.9, standard library only."""
import hashlib, random
from dataclasses import dataclass, field
from typing import List, Optional, Dict

HEADER = "import Mathlib\n"

def rng_for(key, seed, difficulty):
    h = hashlib.sha256(("%s|%d|%d" % (key, seed, difficulty)).encode()).digest()
    return random.Random(int.from_bytes(h[:8], "big"))

@dataclass
class Theorem:
    name: str            # Lean identifier
    statement: str       # everything between the name and `:=`, e.g. "(x : ℝ) : x + 0 = x"
    proof: str           # reference proof: everything after `:=`, e.g. "by\n  simp"
    informal: str = ""   # the statement in words; becomes the doc comment
    weight: float = 1.0

@dataclass
class Task:
    env: str
    family: str
    seed: int
    difficulty: int
    title: str
    informal: str                       # the problem in words (Markdown, maths in \( \))
    kind: str = "prove"                 # "prove" or "define"
    preamble: str = ""                  # Lean text after the import: opens and fixed definitions
    theorems: List[Theorem] = field(default_factory=list)
    # define tasks only
    stub: str = ""                      # what the solver sees, with `sorry` for each definition
    solution: str = ""                  # reference definitions
    free: List[str] = field(default_factory=list)   # names the solver defines
    tests: List[Theorem] = field(default_factory=list)  # hidden; proved by the grader with native_decide
    examples: str = ""                  # public example values, shown in the instruction
    meta: Dict = field(default_factory=dict)

    def _doc(self, t):
        return ("/-- %s -/\n" % t.informal.replace("-/", "- /")) if t.informal else ""

    def _body(self, proofs, defs):
        out = [HEADER]
        if self.preamble.strip(): out.append(self.preamble.strip() + "\n")
        if defs.strip(): out.append(defs.strip() + "\n")
        for t in self.theorems:
            out.append("%stheorem %s %s := %s\n" % (self._doc(t), t.name, t.statement.strip(), t.proof.strip() if proofs else "by\n  sorry"))
        return "\n".join(out)

    def start_file(self):
        """Solution.lean as the solver first sees it."""
        return self._body(False, self.stub)

    def reference_solution(self):
        return self._body(True, self.solution)

    def hidden_reference(self):
        text = self._body(False, self.stub)
        for t in self.tests:
            text += "\ntheorem %s %s := by\n  sorry\n" % (t.name, t.statement.strip())
        return text

    def hidden_tests(self):
        if not self.tests: return None
        text = "import Solution\n"
        for t in self.tests:
            text += "\ntheorem %s %s := by\n  native_decide\n" % (t.name, t.statement.strip())
        return text

    def spec(self):
        graded = self.tests if self.tests else self.theorems
        s = {"reference": self.hidden_reference(), "targets": [{"name": t.name, "weight": t.weight} for t in graded]}
        if self.tests: s["tests"] = self.hidden_tests()
        if self.free: s["free"] = list(self.free)
        return s

    def instruction(self):
        lines = ["# %s" % self.title, "", self.informal.strip(), ""]
        if self.kind == "prove":
            n = len(self.theorems)
            lines += ["## What to do", "",
                "`Solution.lean` in the working directory states %s in Lean 4 with Mathlib, with `sorry` in place of %s. Replace every `sorry` with a proof." % (
                    "the theorem" if n == 1 else "%d theorems" % n, "the proof" if n == 1 else "each proof"),
                "", "- Do not change the statement of any theorem or any definition the file gives you. You may add your own lemmas and definitions.",
                "- Check your work with `lake env lean Solution.lean` (run it inside `/opt/arena/lean`, giving the full path to the file). It must compile without errors.",
                "- A theorem counts only if its proof is complete: no `sorry`, no new axioms, no `native_decide`.",
                ("- The reward is 1 if the theorem is proved and 0 otherwise." if n == 1 else
                 "- The reward is the share of the %d theorems that are proved. If the file does not compile the reward is 0, so leave `sorry` on a theorem you cannot finish rather than a broken proof." % n)]
        else:
            lines += ["## What to do", "",
                "`Solution.lean` in the working directory declares %s with `sorry` as its body. Replace each `sorry` with a definition that matches the description above." % ", ".join("`%s`" % f for f in self.free),
                "", "- Keep the name and the type exactly as given. You may add helper definitions.",
                "- The definition must be computable: it is checked by running it on hidden inputs, so do not use `noncomputable` or classical choice.",
                "- Check that the file compiles with `lake env lean Solution.lean` (run it inside `/opt/arena/lean`, giving the full path to the file), and test your definition with `#eval`.",
                "- The reward is 1 if the definition agrees with the description on every hidden input, and 0 otherwise."]
            if self.examples.strip(): lines += ["", "## Examples", "", self.examples.strip()]
        return "\n".join(lines) + "\n"
