"""Regression tests for envs/real_analysis: exact statements for fixed seeds and hand-checked values."""
import os, re, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from envs.real_analysis import gen


def stmts(seed, d, fam):
    return [t.statement.replace("\n    ", " ") for t in gen.generate(seed, d, fam).theorems]


def test_helpers():
    assert gen.lit(3) == "(3 : ℝ)" and gen.lit(-2) == "(-2 : ℝ)" and gen.lit(F(6, 4)) == "(3 / 2 : ℝ)"
    assert gen.ptex((7, "x"), (-5, "")) == "7x - 5" and gen.ptex((-1, "x^2"), (6, "")) == "-x^2 + 6"


def test_limit_sequence():
    # 8 / (n + 8) -> 0; N = ceil(8 / eps) works because 8 / (n + 8) < 8 / n <= eps
    assert stmts(3, 1, "limit_sequence") == [": ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |(8 : ℝ) / ((n : ℝ) + (8 : ℝ)) - 0| < ε"]
    # (-n - 3) / (4n + 8) -> -1/4: the difference is (4 * (-3) - (-1) * 8) / (4 (4n + 8)) = -4 / (4 (4n + 8))
    assert stmts(3, 2, "limit_sequence") == [": ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |((-1 : ℝ) * (n : ℝ) + (-3 : ℝ)) / ((4 : ℝ) * (n : ℝ) + (8 : ℝ)) - (-1 : ℝ) / (4 : ℝ)| < ε"]
    n = 10
    assert F(-1 * n - 3, 4 * n + 8) - F(-1, 4) == F(4 * -3 - (-1) * 8, 4 * (4 * n + 8)) == F(-4, 4 * 48)
    # (7n + 5) / (n^2 + 4) <= (7 + 5) / n for n >= 1; at n = 3: 26/13 = 2 <= 4
    assert stmts(3, 3, "limit_sequence") == [": ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |((7 : ℝ) * (n : ℝ) + (5 : ℝ)) / ((n : ℝ) ^ 2 + (4 : ℝ)) - 0| < ε"]
    assert F(7 * 3 + 5, 9 + 4) == 2 <= F(12, 3)


def test_continuity():
    # f(x) = 7x + 1 at x0 = -4: f(x) - f(x0) = 7 (x + 4), so delta = eps / 7
    assert stmts(3, 1, "continuity") == [": ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - (-4 : ℝ)| < δ → |((7 : ℝ) * x + (1 : ℝ)) - ((7 : ℝ) * (-4 : ℝ) + (1 : ℝ))| < ε"]
    assert (7 * 5 + 1) - (7 * -4 + 1) == 7 * (5 - -4)
    # 4 / x at x0 = 5 (seed 2): |4/x - 4/5| = 4 |5 - x| / (5 x)
    assert stmts(2, 3, "continuity") == [": ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - (5 : ℝ)| < δ → |(4 : ℝ) / x - (4 : ℝ) / (5 : ℝ)| < ε"]
    assert F(4, 6) - F(4, 5) == F(4 * (5 - 6), 6 * 5)
    # quadratic: the bound constant is A (2 |x0| + 1); at x0 = 0, a = -1 it is 1, and |x^2| < |x| when |x| < 1
    assert stmts(3, 2, "continuity")[0].startswith(": ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - (0 : ℝ)| < δ → |((-1 : ℝ) * x ^ 2 + (6 : ℝ))")
    assert "min 1 (ε / (1 : ℝ))" in gen.generate(3, 2, "continuity").theorems[0].proof


def test_sequence_bounds():
    # a_0 = 8/3, a_{n+1} = a_n / 2 + 8/3: fixed point 16/3, so 0 <= a_n <= 16/3 (a_1 = 4/3 + 8/3 = 4)
    t = gen.generate(3, 1, "sequence_bounds")
    assert t.preamble == "noncomputable def a : ℕ → ℝ\n  | 0 => (8 / 3 : ℝ)\n  | (n + 1) => a n / 2 + (8 / 3 : ℝ)"
    assert stmts(3, 1, "sequence_bounds") == [": ∀ n : ℕ, 0 ≤ a n ∧ a n ≤ (16 / 3 : ℝ)"]
    assert F(8, 3) / 2 + F(8, 3) == 4 and 2 * F(8, 3) == F(16, 3)
    # difficulty 3: a_0 = 4/15, a_{n+1} = (a_n^2 + 24/25) / 2; fixed points are 1 - s and 1 + s with s = 1/5, and 1 - s = 4/5
    t = gen.generate(3, 3, "sequence_bounds")
    assert "(n + 1) => (a n ^ 2 + (24 / 25 : ℝ)) / 2" in t.preamble
    assert stmts(3, 3, "sequence_bounds") == [": ∀ n : ℕ, 0 ≤ a n ∧ a n ≤ (4 / 5 : ℝ)", ": Monotone a"]
    s = F(1, 5)
    assert 1 - s * s == F(24, 25) and (F(4, 5) ** 2 + F(24, 25)) / 2 == F(4, 5) and t.theorems[1].weight == 2.0


def test_uniform_bounds():
    # on [-2/3, 2/3]: |8 x^(n+1)| <= 8 (2/3)^(n+1)
    assert stmts(3, 1, "uniform_bounds") == [": ∀ n : ℕ, ∀ x ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3 : ℝ), |8 * x ^ (n + 1)| ≤ 8 * (2 / 3 : ℝ) ^ (n + 1)"]
    # geometric sum on [0, 4/5]: the bound is 1 / (1 - 4/5) = 5, and the sum of (4/5)^i for i < 3 is 1 + 4/5 + 16/25 = 61/25 < 5
    assert stmts(3, 2, "uniform_bounds") == [": ∀ n : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) (4 / 5 : ℝ), ∑ i ∈ Finset.range n, x ^ i ≤ 1 / (1 - (4 / 5 : ℝ))"]
    assert 1 + F(4, 5) + F(16, 25) == F(61, 25) < 1 / (1 - F(4, 5)) == 5
    # uniform convergence on |x| <= 2/5 with constant 9
    assert stmts(3, 3, "uniform_bounds") == [": ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |x| ≤ (2 / 5 : ℝ) → |9 * x ^ n| < ε"]
