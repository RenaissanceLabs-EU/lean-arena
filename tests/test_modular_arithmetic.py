"""Regression tests for envs/modular_arithmetic: exact statements for fixed seeds and hand-checked values."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from envs.modular_arithmetic import gen


def stmts(seed, d, fam):
    return [t.statement.replace("\n    ", " ") for t in gen.generate(seed, d, fam).theorems]


def test_power_residues():
    # 5 n^2 + 5 mod 8: squares mod 8 are 0, 1, 4, so the values are 5, 10 = 2, 25 = 1
    assert stmts(0, 1, "power_residues") == ["(n : ℕ) : (5 * n ^ 2 + 5) % 8 = 1 ∨ (5 * n ^ 2 + 5) % 8 = 2 ∨ (5 * n ^ 2 + 5) % 8 = 5"]
    # cubes mod 9 are 0, 1, 8, so 2a^3 + b^3 + 1 takes 1,2,0,3,4,8,7 and never 5
    assert stmts(0, 3, "power_residues") == ["(a b : ℕ) : (2 * a ^ 3 + b ^ 3 + 1) % 9 ≠ 5"]
    assert {(2 * a ** 3 + b ** 3 + 1) % 9 for a in range(9) for b in range(9)} == {0, 1, 2, 3, 4, 7, 8}


def test_divisibility():
    # 29 n^3 - 23 n = 29 (n^3 - n) + 6 n, divisible by 6
    assert stmts(0, 1, "divisibility") == ["(n : ℤ) : (6 : ℤ) ∣ 29 * n ^ 3 - 23 * n"]
    # 23 + 7 = 30, so 23 n^5 + 7 n = 23 (n^5 - n) + 30 n is divisible by 30 = 2 * 3 * 5
    s = stmts(0, 3, "divisibility")
    assert s[0] == "(n : ℤ) : (2 : ℤ) ∣ 23 * n ^ 5 + 7 * n" and s[-1] == "(n : ℤ) : (30 : ℤ) ∣ 23 * n ^ 5 + 7 * n"
    assert len(s) == 4 and gen.generate(0, 3, "divisibility").theorems[-1].weight == 3.0


def test_congruence_chain():
    assert stmts(0, 1, "congruence_chain") == ["(x : ℤ) (h : x ≡ 0 [ZMOD 8]) : x ^ 2 + 5 * x + 1 ≡ 1 [ZMOD 8]"]
    # 5^31 = 5 mod 10 and 9^31 = 9 mod 10, so 5 * 9 + 6 = 51 = 1 mod 10
    s = stmts(0, 3, "congruence_chain")
    assert s == ["(x : ℤ) (h : x ≡ 5 [ZMOD 10]) : x ^ 31 ≡ 5 [ZMOD 10]",
                 "(x y : ℤ) (hx : x ≡ 5 [ZMOD 10]) (hy : y ≡ 9 [ZMOD 10]) : x ^ 31 * y ^ 31 + 6 ≡ 1 [ZMOD 10]"]
    assert pow(5, 31, 10) == 5 and pow(9, 31, 10) == 9 and (5 * 9 + 6) % 10 == 1


def test_gcd_coprime():
    # determinant 1 * 28 - 3 * 9 = 1
    assert stmts(0, 1, "gcd_coprime") == ["(n : ℤ) : IsCoprime (n + 3) (9 * n + 28)"]
    assert 1 * 28 - 3 * 9 == 1
    # determinant 3 * 6 - 3 * 7 = -3, a prime, so the gcd divides 3
    s = stmts(0, 3, "gcd_coprime")
    assert s[0] == "(n : ℕ) : Nat.gcd (3 * n + 3) (7 * n + 6) ∣ 3"
    assert s[1] == "(n : ℕ) : Nat.gcd (3 * n + 3) (7 * n + 6) = 1 ∨ Nat.gcd (3 * n + 3) (7 * n + 6) = 3"
    assert 3 * 6 - 3 * 7 == -3


def test_general():
    for fam in gen.FAMILIES:
        for d in (1, 2, 3):
            t = gen.generate(4, d, fam)
            assert t.kind == "prove" and t.family == fam and "sorry" in t.start_file() and "sorry" not in t.reference_solution()


if __name__ == "__main__":
    for k, v in list(globals().items()):
        if k.startswith("test_"): v()
    print("ok")
