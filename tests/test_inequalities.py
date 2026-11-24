"""Regression tests for envs/inequalities: exact statements for fixed seeds and hand-checked values."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from envs.inequalities import gen


def stmts(seed, d, fam):
    return [t.statement.replace("\n    ", " ") for t in gen.generate(seed, d, fam).theorems]


def test_amgm():
    # 4 * 2 * 6 = 48 and (2a + 6b)^2 - 48ab = (2a - 6b)^2
    assert stmts(0, 1, "amgm") == ["(a b : ℝ) : 48 * a * b ≤ (2 * a + 6 * b) ^ 2"]
    # 27 * (4 * 4 * 3) = 1296
    s = stmts(0, 3, "amgm")
    assert s[1] == "(a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 1296 * a * b * c ≤ (4 * a + 4 * b + 3 * c) ^ 3"
    assert 27 * 4 * 4 * 3 == 1296 and len(s) == 2


def test_cauchy():
    # 9^2 + 1^2 = 82
    assert stmts(0, 1, "cauchy") == ["(x y : ℝ) : (9 * x + y) ^ 2 ≤ 82 * (x ^ 2 + y ^ 2)"]
    # 2^2 + 6^2 + 9^2 = 121 = 11^2 and the ball has radius 4, so the bound is 44
    s = stmts(0, 3, "cauchy")
    assert s[1] == "(x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 ≤ 16) : 2 * x - 6 * y - 9 * z ≤ 44"
    assert 2 ** 2 + 6 ** 2 + 9 ** 2 == 11 ** 2 and 11 * 4 == 44


def test_abs_ineq():
    # p = 5, q = 9, a = -1, b = 9: constant 5 * (-1) - 9 * 9 = -86, bound 5 * 2 + 9 * 4 = 46
    assert stmts(0, 1, "abs_ineq") == ["(x y : ℝ) (hx : |x + 1| ≤ 2) (hy : |y - 9| ≤ 4) : |5 * x - 9 * y + 86| ≤ 46"]
    assert 5 * (-1) - 9 * 9 == -86 and 5 * 2 + 9 * 4 == 46
    # (9 - 4) + (8 - 6) = 7
    assert stmts(0, 3, "abs_ineq")[1] == "(x : ℝ) : 7 ≤ |x - 4| + |x - 6| + |x - 8| + |x - 9|"
    assert (9 - 4) + (8 - 6) == 7


def test_monotone():
    s = stmts(0, 1, "monotone")
    assert s == ["(x y : ℝ) (h : x ≤ y) : Real.sinh x + 6 * x ≤ Real.sinh y + 6 * y"]
    t = gen.generate(0, 3, "monotone")
    assert [x.name for x in t.theorems] == ["log_one_add_sq_mono", "monotone_combination"]
    assert "Real.log (1 + y ^ 2)" in t.theorems[1].statement and t.theorems[1].weight == 2.0
    t2 = gen.generate(0, 2, "monotone")
    assert t2.theorems[0].statement.startswith(": Monotone (fun x : ℝ =>")


def test_general():
    for fam in gen.FAMILIES:
        for d in (1, 2, 3):
            t = gen.generate(4, d, fam)
            assert t.kind == "prove" and t.family == fam and "sorry" in t.start_file() and "sorry" not in t.reference_solution()


if __name__ == "__main__":
    for k, v in list(globals().items()):
        if k.startswith("test_"): v()
    print("ok")
