"""Regression tests for envs/linear_algebra/gen.py (plain asserts)."""
import re
from envs.linear_algebra.gen import generate, FAMILIES, mm, det2, tr2

def stmts(t): return [re.sub(r"\s+", " ", x.statement) for x in t.theorems]

# det_trace: det(AB) = det(A) det(B) worked by hand; charpoly constants
t = generate(0, 1, "det_trace")
assert stmts(t)[0] == ": Matrix.det (!![-2, 3; 3, 0] * !![-2, 4; 3, 0] : Matrix (Fin 2) (Fin 2) ℤ) = 108", stmts(t)
assert det2([[-2, 3], [3, 0]]) == -9 and det2([[-2, 4], [3, 0]]) == -12 and (-9) * (-12) == 108
assert mm([[-2, 3], [3, 0]], [[-2, 4], [3, 0]]) == [[13, -8], [-6, 12]] and det2([[13, -8], [-6, 12]]) == 156 - 48
t = generate(0, 2, "det_trace")
assert stmts(t)[0] == "(x : ℤ) : Matrix.det (x • (1 : Matrix (Fin 2) (Fin 2) ℤ) - !![2, 1; 3, 3]) = x ^ 2 - 5 * x + 3", stmts(t)
assert tr2([[2, 1], [3, 3]]) == 5 and det2([[2, 1], [3, 3]]) == 3
t = generate(0, 3, "det_trace")
assert [x.name for x in t.theorems] == ["cayley_hamilton_two", "cube_of_matrix"]
m = re.search(r"trace A = \((-?\d+) : ℤ\)\) \(hd : Matrix.det A = \((-?\d+) : ℤ\)\) : A \^ 3 = \((-?\d+) : ℤ\) • A - \((-?\d+) : ℤ\)", stmts(t)[1])
tt, dd, c1, c0 = map(int, m.groups()); assert (c1, c0) == (tt * tt - dd, tt * dd) and (tt, dd) == (2, -1) and (c1, c0) == (5, -2)

# matrix_pow: exact forms and a hand-computed power
t = generate(0, 1, "matrix_pow")
assert stmts(t)[0] == "(n : ℕ) : (!![1, 7; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ n = !![1, (n : ℤ) * 7; 0, 1]", stmts(t)
P = [[1, 0], [0, 1]]
for _ in range(4): P = mm(P, [[1, 7], [0, 1]])
assert P == [[1, 28], [0, 1]]
t = generate(1, 3, "matrix_pow")
assert stmts(t)[0] == "(n : ℕ) : (!![2, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ n = !![2 ^ n, 2 * ∑ i ∈ Finset.range n, 2 ^ i; 0, 1]", stmts(t)
P = [[1, 0], [0, 1]]
for _ in range(3): P = mm(P, [[2, 2], [0, 1]])
assert P == [[8, 2 * (1 + 2 + 4)], [0, 1]]

# independence: determinant of explicit vectors decides the statement
t = generate(0, 1, "independence")
assert stmts(t)[0] == ": LinearIndependent ℚ ![(![-3, 2] : Fin 2 → ℚ), ![3, 3]]", stmts(t)
assert det2([[-3, 2], [3, 3]]) == -15
for s in range(20):
    t = generate(s, 2, "independence"); st = stmts(t)[0]
    v = [[int(x) for x in row.split(",")] for row in re.findall(r"!\[(-?\d+, -?\d+)\]", st)]
    assert len(v) == 2
    assert (det2(v) != 0) == (not st.startswith(": ¬")), st
t = generate(1, 3, "independence")
assert stmts(t)[0] == ": ¬ LinearIndependent ℚ ![(![2, -2, 3] : Fin 3 → ℚ), ![1, 0, 4], ![-1, -2, -9]]", stmts(t)
# the third vector is a combination of the first two: the Fraction rank (second code path) is 2, not 3
from envs.linear_algebra.gen import rank_frac
assert rank_frac([[2, -2, 3], [1, 0, 4], [-1, -2, -9]]) == 2 and rank_frac([[2, -2, 3], [1, 0, 4]]) == 2

# linear_map: exact statements
t = generate(3, 3, "linear_map")
assert [x.name for x in t.theorems] == ["disjoint_ker_range", "ker_range_isCompl"]
assert stmts(t)[0].endswith("(q : V →ₗ[ℝ] V) (hp : q * q = q) : Disjoint (LinearMap.ker q) (LinearMap.range q)"), stmts(t)
t = generate(0, 1, "linear_map")
assert "f ((-3 : ℚ) • a + (3 : ℚ) • b) = 0" in stmts(t)[0], stmts(t)
t = generate(2, 3, "linear_map")
assert stmts(t)[0] == "{V : Type*} [AddCommGroup V] [Module ℚ V] (e : V →ₗ[ℚ] V) (hp : e * e = e) : (LinearMap.id - e) ∘ₗ (LinearMap.id - e) = LinearMap.id - e ∧ e ∘ₗ (LinearMap.id - e) = 0", stmts(t)

for f in FAMILIES:
    for d in (1, 2, 3):
        a, b = generate(7, d, f), generate(7, d, f)
        assert a.reference_solution() == b.reference_solution() and a.kind == "prove" and a.family == f
assert generate(0, 1).family == sorted(FAMILIES)[0] and generate(2, 1).family == sorted(FAMILIES)[2]
print("test_linear_algebra ok")
