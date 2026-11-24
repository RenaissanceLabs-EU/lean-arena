"""Regression tests for envs/combinatorial_identities: exact statements for fixed seeds and hand-checked values."""
import os, re, sys
from math import comb
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from envs.combinatorial_identities import gen


def stmts(seed, d, fam):
    return [t.statement.replace("\n    ", " ") for t in gen.generate(seed, d, fam).theorems]


def test_binomial_sums():
    # sum C(n,i) 2^i = 3^n: n = 2 gives 1 + 2*2 + 4 = 9
    assert stmts(0, 1, "binomial_sums") == ["(n : ℕ) : ∑ i ∈ Finset.range (n + 1), n.choose i * 2 ^ i = 3 ^ n"]
    assert sum(comb(2, i) * 2 ** i for i in range(3)) == 9
    # hockey stick: C(6,6) + C(7,6) + C(8,6) = 1 + 7 + 28 = 36 = C(9,7)
    assert sum(comb(i + 6, 6) for i in range(3)) == comb(9, 7) == 36
    # difficulty 3: lemma sum i C(n,i) = n 2^(n-1), then the weighted sum; n = 3: 0 + 3 + 6 + 3 = 12 = 3 * 4
    ts = gen.generate(0, 3, "binomial_sums").theorems
    assert ts[0].statement.replace("\n    ", " ") == "(n : ℕ) : ∑ i ∈ Finset.range (n + 1), i * n.choose i = n * 2 ^ (n - 1)" and ts[1].weight == 2.0
    assert sum(i * comb(3, i) for i in range(4)) == 12 == 3 * 2 ** 2
    for seed in range(10):
        s = gen.generate(seed, 3, "binomial_sums").theorems[1].statement
        a, c, a2, c2 = map(int, re.search(r"\((\d+) \* i \+ (\d+)\).*= (\d+) \* \(n \* 2 \^ \(n - 1\)\) \+ (\d+) \* 2 \^ n", s).groups())
        assert (a, c) == (a2, c2)
        assert sum((a * i + c) * comb(4, i) for i in range(5)) == a * 4 * 8 + c * 16


def test_fibonacci():
    # F_0..F_8 = 0 1 1 2 3 5 8 13 21; shifted sum with a = 7: F_7 + F_8 + F_9 + F_8 ... check n = 2: 13 + 21 + F_8 = 55 = F_10
    assert stmts(3, 1, "fibonacci") == ["(n : ℕ) : ∑ i ∈ Finset.range n, Nat.fib (i + 7) + Nat.fib 8 = Nat.fib (n + 8)"]
    f = gen.fibs(12)
    assert f[:9] == [0, 1, 1, 2, 3, 5, 8, 13, 21] and f[7] + f[8] + f[8] == 55 == f[10]
    # sum of c F_i^2 for i <= n equals c F_n F_(n+1): 1 + 1 + 4 + 9 = 15 = 3 * 5
    assert stmts(3, 2, "fibonacci") == ["(n : ℕ) : ∑ i ∈ Finset.range (n + 1), 2 * Nat.fib i ^ 2 = 2 * (Nat.fib n * Nat.fib (n + 1))"]
    assert sum(f[i] ** 2 for i in range(5)) == 15 == f[4] * f[5]
    # Cassini: F_3^2 - F_2 F_4 = 4 - 3 = 1 = (-1)^2 ... F_(n+1)^2 - F_n F_(n+2) with n = 2 is 4 - 1*5... use values: F_3 = 2, F_2 = 1, F_4 = 3
    ts = gen.generate(3, 3, "fibonacci").theorems
    assert [t.name for t in ts] == ["cassini", "cassini_pm_one"] and ts[1].weight == 2.0
    assert f[3] ** 2 - f[2] * f[4] == 1 == (-1) ** 2 and f[4] ** 2 - f[3] * f[5] == -1 == (-1) ** 3


def test_linear_recurrence():
    # u_n = 4 * 4^n + 2 * 5^n: u_0 = 6, u_1 = 26, u_2 = 64 + 50 = 114 = 9 * 26 - 20 * 6
    t = gen.generate(0, 1, "linear_recurrence")
    t3 = gen.generate(3, 1, "linear_recurrence")
    assert t3.preamble == "def u : ℕ → ℤ\n  | 0 => 6\n  | 1 => 26\n  | (n + 2) => 9 * u (n + 1) - 20 * u n"
    assert t3.theorems[0].statement.replace("\n    ", " ") == "(n : ℕ) : u n = 4 * 4 ^ n + 2 * 5 ^ n"
    assert 4 * 16 + 2 * 25 == 114 == 9 * 26 - 20 * 6
    # repeated root, difficulty 3: u_n = ((-3) + (-1) n) 3^n has u_0 = -3, u_1 = -12 and u_2 = 6 * (-12) - 9 * (-3) = -45 = (-5) * 9
    t = gen.generate(3, 3, "linear_recurrence")
    assert t.preamble == "def u : ℕ → ℤ\n  | 0 => (-3)\n  | 1 => (-12)\n  | (n + 2) => 6 * u (n + 1) - 9 * u n"
    assert t.theorems[0].statement.replace("\n    ", " ") == "(n : ℕ) : u n = ((-3) + (-1) * (n : ℤ)) * 3 ^ n"
    assert 6 * -12 - 9 * -3 == -45 == (-3 - 2) * 9
    # in every task the recurrence coefficients are (r+s, rs) or (2r, r^2): their discriminant is a square
    for seed in range(15):
        for d in (1, 2, 3):
            pre = gen.generate(seed, d, "linear_recurrence").preamble
            m = re.search(r"\| \(n \+ 2\) => \(?(-?\d+)\)? \* u \(n \+ 1\) - \(?(-?\d+)\)? \* u n", pre)
            p, q = int(m.group(1)), int(m.group(2))
            disc = p * p - 4 * q
            assert disc >= 0 and int(disc ** 0.5) ** 2 == disc
            if d == 3: assert disc == 0


def test_counting():
    # any 6 integers contain two with equal remainder mod 5: here the statement is for 5 < card
    assert stmts(0, 1, "counting") == ["(s : Finset ℤ) (h : 5 < s.card) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x % 5 = y % 5"]
    # residue class 1 mod 5 below 5n has exactly n elements (1, 6, 11, ...), so the injection x -> 5x + 1 is a bijection
    assert stmts(3, 2, "counting") == ["(n : ℕ) : (Finset.range n).card ≤ ((Finset.range (5 * n)).filter (fun y => y % 5 = 1)).card"]
    assert len([y for y in range(5 * 4) if y % 5 == 1]) == 4
    # blocks: s inside range (k * m) with more than m elements has two elements closer than k
    assert stmts(3, 3, "counting") == ["(s : Finset ℕ) (hs : s ⊆ Finset.range (6 * 4)) (h : 4 < s.card) : ∃ x ∈ s, ∃ y ∈ s, x < y ∧ y < x + 6"]
    # sharpness by hand: m elements 0, k, 2k, ... (m - 1) k are pairwise at distance at least k
    k, m = 6, 4
    pts = [i * k for i in range(m)]
    assert all(b - a >= k for a, b in zip(pts, pts[1:])) and max(pts) < k * m
