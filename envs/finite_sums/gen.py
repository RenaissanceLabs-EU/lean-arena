"""Closed forms for finite sums (MSC 40: sequences, series, summability; 05A19 identities).

Formulas: sum_{i=0}^{n} i = n(n+1)/2, sum i^2 = n(n+1)(2n+1)/6, sum i^3 = n^2(n+1)^2/4;
geometric (r-1) * sum_{i<n} c r^i = c (r^n - 1); telescoping sum_{i<n} 1/((i+a)(i+a+1)) = n/(a(n+a)).
Second code path: every generated identity is checked numerically with exact fractions before
it is returned; the Lean reference proof is compiled in the self-test.
"""
from fractions import Fraction as F
from arena.core import Task, Theorem, rng_for

ENV = "finite_sums"
FAMILIES = ["geometric", "polynomial", "telescoping"]
IND = "by\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    rw [Finset.sum_range_succ, ih]\n    push_cast\n    ring"

def term(c, var, power):
    """Lean text for c * var^power, with c a nonzero int."""
    v = "" if power == 0 else ("(%s : ℚ)" % var if power == 1 else "(%s : ℚ) ^ %d" % (var, power))
    if power == 0: return "%d" % c
    return v if c == 1 else "%d * %s" % (c, v)

def tex_poly(cs, var):
    out = []
    for power in range(len(cs) - 1, -1, -1):
        c = cs[power]
        if not c: continue
        v = "" if power == 0 else (var if power == 1 else "%s^%d" % (var, power))
        mag = abs(c); body = v if (mag == 1 and power) else "%d%s" % (mag, v)
        out.append(("- " if c < 0 else ("+ " if out else "")) + body)
    return " ".join(out)

def polynomial(rng, difficulty):
    deg = difficulty
    while True:
        cs = [rng.randrange(-4, 6) for _ in range(deg + 1)]      # cs[p] multiplies i^p
        if cs[deg] > 0 and sum(1 for c in cs if c) >= min(2, deg + 1): break
    summand = " + ".join(term(c, "i", p) for p, c in reversed(list(enumerate(cs))) if c)
    n = "(n : ℚ)"
    closed = {0: "(%s + 1)" % n, 1: "%s * (%s + 1) / 2" % (n, n), 2: "%s * (%s + 1) * (2 * %s + 1) / 6" % (n, n, n), 3: "%s ^ 2 * (%s + 1) ^ 2 / 4" % (n, n)}
    rhs = " + ".join(("%d * (%s)" % (c, closed[p])) for p, c in reversed(list(enumerate(cs))) if c)
    def lhs_val(m): return sum(sum(F(c) * i ** p for p, c in enumerate(cs)) for i in range(m + 1))
    def rhs_val(m):
        cl = {0: F(m + 1), 1: F(m * (m + 1), 2), 2: F(m * (m + 1) * (2 * m + 1), 6), 3: F(m * m * (m + 1) ** 2, 4)}
        return sum(c * cl[p] for p, c in enumerate(cs))
    assert all(lhs_val(m) == rhs_val(m) for m in range(8))
    tex_closed = {0: "(n+1)", 1: "\\frac{n(n+1)}{2}", 2: "\\frac{n(n+1)(2n+1)}{6}", 3: "\\frac{n^2(n+1)^2}{4}"}
    tex_rhs = " + ".join("%d \\cdot %s" % (c, tex_closed[p]) for p, c in reversed(list(enumerate(cs))) if c).replace("+ -", "- ")
    informal = "For every natural number \\(n\\), \\[\\sum_{i=0}^{n} \\left(%s\\right) = %s.\\]" % (tex_poly(cs, "i"), tex_rhs)
    stmt = "(n : ℕ) :\n    ∑ i ∈ Finset.range (n + 1), (%s) = %s" % (summand, rhs)
    return informal, stmt, IND

def geometric(rng, difficulty):
    r = rng.choice([2, 3, 4, 5, 6, 7, 8, 9] if difficulty < 3 else [-2, -3, -4, 3, 5, 6, 7]); c = rng.randrange(1, 10) if difficulty > 1 else rng.choice([1, 1, 2, 3])
    shift = rng.randrange(1, 4) if difficulty == 3 else 0
    rl = "(%d : ℤ)" % r
    summand = ("%d * " % c if c != 1 else "") + "%s ^ (i + %d)" % (rl, shift) if shift else ("%d * " % c if c != 1 else "") + "%s ^ i" % rl
    stmt = "(n : ℕ) :\n    (%d : ℤ) * ∑ i ∈ Finset.range n, %s = %d * (%s ^ n - 1)" % (r - 1, summand, c * r ** shift, rl)
    assert all((r - 1) * sum(c * r ** (i + shift) for i in range(m)) == c * r ** shift * (r ** m - 1) for m in range(8))
    tex_r = "(%d)" % r if r < 0 else "%d" % r
    informal = "For every natural number \\(n\\), \\[%d \\sum_{i=0}^{n-1} %s%s^{%s} = %d\\left(%s^{n} - 1\\right).\\] The sum is over the integers and is empty when \\(n = 0\\)." % (
        r - 1, ("%d \\cdot " % c) if c != 1 else "", tex_r, "i+%d" % shift if shift else "i", c * r ** shift, tex_r)
    proof = "by\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    rw [Finset.sum_range_succ, mul_add, ih]\n    ring"
    return informal, stmt, proof

def telescoping(rng, difficulty):
    a = rng.randrange(1, 5) if difficulty == 1 else rng.randrange(2, 9); c = rng.choice([1, 1, 2]) if difficulty < 3 else rng.randrange(2, 9)
    # sum_{i<n} c / ((i+a)(i+a+1)) = c n / (a (n+a))
    stmt = "(n : ℕ) :\n    ∑ i ∈ Finset.range n, (%d : ℚ) / (((i : ℚ) + %d) * ((i : ℚ) + %d)) = %d * (n : ℚ) / (%d * ((n : ℚ) + %d))" % (c, a, a + 1, c, a, a)
    assert all(sum(F(c, (i + a) * (i + a + 1)) for i in range(m)) == F(c * m, a * (m + a)) for m in range(8))
    informal = "For every natural number \\(n\\), \\[\\sum_{i=0}^{n-1} \\frac{%d}{(i+%d)(i+%d)} = \\frac{%s}{%s}.\\] The sum is over the rationals and is empty when \\(n = 0\\)." % (
        c, a, a + 1, ("%dn" % c) if c != 1 else "n", ("%d(n+%d)" % (a, a)) if a != 1 else "n+1")
    proof = ("by\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    rw [Finset.sum_range_succ, ih]\n"
             "    have h1 : ((k : ℚ) + %d) ≠ 0 := by positivity\n    have h2 : ((k : ℚ) + %d) ≠ 0 := by positivity\n"
             "    have h3 : (((k + 1 : ℕ) : ℚ) + %d) ≠ 0 := by positivity\n    push_cast\n    field_simp\n    ring") % (a, a + 1, a)
    return informal, stmt, proof

def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    informal, stmt, proof = {"polynomial": polynomial, "geometric": geometric, "telescoping": telescoping}[family](rng, difficulty)
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove",
        title="Prove a closed form for a finite sum", informal="Prove the following identity.\n\n" + informal,
        theorems=[Theorem("sum_closed_form", stmt, proof, "The closed form stated in the task.")])
