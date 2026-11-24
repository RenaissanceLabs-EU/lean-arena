"""Linear algebra (MSC 15: linear and multilinear algebra, matrix theory).

Families: det_trace (determinant, trace and Cayley-Hamilton for 2x2 integer matrices),
matrix_pow (closed forms for powers of 2x2 matrices by induction), independence (linear
independence or dependence of explicit vectors in Fin 2 -> Q and Fin 3 -> Q), linear_map
(kernel, range and idempotent maps on vector spaces).
Second code path: every numeric claim is re-checked in Python with exact integer or Fraction
arithmetic (matrix products, determinants, Gaussian elimination) before the task is returned;
the Lean reference proofs are compiled in the self-test.
"""
from fractions import Fraction as F
from arena.core import Task, Theorem, rng_for

ENV = "linear_algebra"
FAMILIES = ["det_trace", "independence", "linear_map", "matrix_pow"]
M2 = "Matrix (Fin 2) (Fin 2) ℤ"

def mm(A, B): return [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def det2(A): return A[0][0] * A[1][1] - A[0][1] * A[1][0]
def tr2(A): return A[0][0] + A[1][1]
def mat(A): return "!![%s]" % "; ".join(", ".join(str(x) for x in row) for row in A)
def tex(A): return "\\begin{pmatrix} %s \\end{pmatrix}" % " \\\\ ".join(" & ".join(str(x) for x in row) for row in A)
def rmat(rng, lo, hi): return [[rng.randrange(lo, hi + 1) for _ in range(2)] for _ in range(2)]
def zn(x): return "(%d : ℤ)" % x
def num(x): return "(%d : ℤ)" % x if x < 0 else str(x)

FIN2 = "rw [Matrix.one_fin_two, Matrix.mul_fin_two]\n  ext i j\n  fin_cases i <;> fin_cases j <;> simp <;> ring"

# ---------------------------------------------------------------- det_trace

CAYLEY = Theorem("cayley_hamilton_two", "(A : %s) :\n    A ^ 2 = Matrix.trace A • A - Matrix.det A • (1 : %s)" % (M2, M2),
                 "by\n  rw [Matrix.eta_fin_two A, Matrix.one_fin_two, pow_two, Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]\n  ext i j\n  fin_cases i <;> fin_cases j <;> simp <;> ring",
                 "Cayley-Hamilton for 2x2 integer matrices.", 0.4)

def det_trace(rng, difficulty):
    kind = rng.choice({1: ["detprod", "adjugate"], 2: ["charpoly", "cayley", "detprodx"], 3: ["cayley3", "trace_sq"]}[difficulty])
    if kind in ("detprod", "detprod3"):
        k = 2 if kind == "detprod" else 3
        Ms = [rmat(rng, -3, 4) for _ in range(k)]
        P = Ms[0]
        for X in Ms[1:]: P = mm(P, X)
        v = 1
        for X in Ms: v *= det2(X)
        assert det2(P) == v and all(det2(mm(X, Y)) == det2(X) * det2(Y) for X in Ms for Y in Ms)
        if abs(v) < 2 and difficulty > 1: return det_trace(rng, difficulty)
        prod = " * ".join(mat(X) for X in Ms)
        rw = ", ".join(["Matrix.det_mul"] * (k - 1) + ["Matrix.det_fin_two_of"] * k)
        informal = "Compute the determinant of the product %s of integer matrices. Show that it equals %d." % (" ".join("\\(%s\\)" % tex(X) for X in Ms), v)
        return informal, [Theorem("det_of_product", ": Matrix.det (%s : %s) = %s" % (prod, M2, num(v)), "by\n  rw [%s]\n  norm_num" % rw, "The determinant of the product is the product of the determinants.")]
    if kind == "detprodx":
        p, q, r, s_ = [rng.randrange(-3, 4) for _ in range(4)]; u, v, w = [rng.randrange(-3, 4) for _ in range(3)]
        A = lambda x: [[x + p, q], [r, x + s_]]; B = lambda x: [[x, u], [v, x + w]]
        pa = [p * s_ - q * r, p + s_, 1]; pb = [-u * v, w, 1]
        prod = [sum(pa[i] * pb[k - i] for i in range(3) if 0 <= k - i < 3) for k in range(5)]
        for x in range(-4, 5):
            assert det2(mm(A(x), B(x))) == sum(c * x ** i for i, c in enumerate(prod))
        if prod[0] == 0 and prod[1] == 0: return det_trace(rng, difficulty)
        def e(c): return "x + %d" % c if c >= 0 else "x - %d" % -c
        La = "!![%s, %d; %d, %s]" % (e(p), q, r, e(s_)); Lb = "!![x, %d; %d, %s]" % (u, v, e(w))
        poly = " + ".join("%d * x ^ %d" % (c, i) if i > 1 else ("%d * x" % c if i == 1 else "%d" % c) for i, c in reversed(list(enumerate(prod))) if c)
        poly = poly.replace("+ -", "- ").replace("1 * x", "x") if False else poly
        def poly_str(cs, times, pw):
            out = ""
            for i in range(len(cs) - 1, -1, -1):
                c = cs[i]
                if not c: continue
                mag = abs(c); body = ("%d" % mag) if i == 0 else (("x" if i == 1 else pw % i) if mag == 1 else "%d%sx%s" % (mag, times, "" if i == 1 else pw % i if False else (pw % i)[1:]) if False else (("%d%s" % (mag, times) + ("x" if i == 1 else pw % i))))
                out += (("-" if c < 0 else "") + body) if not out else (" - " if c < 0 else " + ") + body
            return out
        stmt = "(x : ℤ) :\n    Matrix.det (%s * %s : %s) = %s" % (La, Lb, M2, poly_str(prod, " * ", "x ^ %d"))
        informal = "For every integer \\(x\\), the determinant of \\[\\begin{pmatrix} x%+d & %d \\\\ %d & x%+d \\end{pmatrix}\\begin{pmatrix} x & %d \\\\ %d & x%+d \\end{pmatrix}\\] equals \\(%s\\)." % (
            p, q, r, s_, u, v, w, poly_str(prod, "", "x^%d"))
        return informal, [Theorem("det_of_polynomial_product", stmt, "by\n  rw [Matrix.det_mul, Matrix.det_fin_two_of, Matrix.det_fin_two_of]\n  ring", "The determinant of a product of matrices with a variable entry.")]
    if kind == "adjugate":
        p, q, r, s = [rng.randrange(-3, 5) for _ in range(4)]
        A = lambda x: [[x + p, q], [r, x + s]]; Adj = lambda x: [[x + s, -q], [-r, x + p]]
        for x in range(-4, 5):
            P = mm(A(x), Adj(x)); d = x * x + (p + s) * x + (p * s - q * r)
            assert P == [[d, 0], [0, d]]
        def ent(top, a, b): return "x + %d" % top if top >= 0 else "x - %d" % -top
        def e(c): return "x + %d" % c if c >= 0 else "x - %d" % -c
        L = "!![%s, %d; %d, %s]" % (e(p), q, r, e(s)); R = "!![%s, %d; %d, %s]" % (e(s), -q, -r, e(p))
        poly = "x ^ 2 + %d * x + %d" % (p + s, p * s - q * r)
        stmt = "(x : ℤ) :\n    %s * %s = (%s) • (1 : %s)" % (L, R, poly, M2)
        proof = "by\n  " + FIN2
        informal = "For every integer \\(x\\), \\[\\begin{pmatrix} x%+d & %d \\\\ %d & x%+d \\end{pmatrix}\\begin{pmatrix} x%+d & %d \\\\ %d & x%+d \\end{pmatrix} = (x^2 %+d x %+d) \\begin{pmatrix} 1 & 0 \\\\ 0 & 1 \\end{pmatrix}.\\]" % (p, q, r, s, s, -q, -r, p, p + s, p * s - q * r)
        return informal, [Theorem("adjugate_product", stmt, proof, "A matrix times its adjugate is its determinant times the identity.")]
    if kind == "charpoly":
        A = rmat(rng, -3, 4)
        T, D = tr2(A), det2(A)
        for x in range(-5, 6): assert det2([[x - A[0][0], -A[0][1]], [-A[1][0], x - A[1][1]]]) == x * x - T * x + D
        poly = "x ^ 2 - %s * x + %s" % (num(T), num(D))
        stmt = "(x : ℤ) :\n    Matrix.det (x • (1 : %s) - %s) = %s" % (M2, mat(A), poly)
        informal = "For every integer \\(x\\), the determinant of \\(x I - %s\\), where \\(I\\) is the \\(2 \\times 2\\) identity matrix, equals \\(x^2 - (%d)x + (%d)\\)." % ("\\(%s\\)" % tex(A) if False else tex(A), T, D)
        informal = "For every integer \\(x\\), \\[\\det\\left(x I - %s\\right) = x^2 - (%d)\\,x + (%d),\\] where \\(I\\) is the \\(2 \\times 2\\) identity matrix." % (tex(A), T, D)
        return informal, [Theorem("char_poly_value", stmt, "by\n  rw [Matrix.one_fin_two, Matrix.det_fin_two]\n  simp\n  ring", "The characteristic polynomial of a 2x2 matrix is x^2 - tr x + det.")]
    # Cayley-Hamilton based
    t, d = rng.randrange(-3, 4), rng.randrange(-4, 5)
    # second path: A^2 - tr A + det I = 0 on random integer matrices
    for _ in range(20):
        B = rmat(rng, -5, 5); B2 = mm(B, B)
        for i in range(2):
            for j in range(2): assert B2[i][j] - tr2(B) * B[i][j] + det2(B) * (1 if i == j else 0) == 0
        B3 = mm(B2, B)
        for i in range(2):
            for j in range(2): assert B3[i][j] == (tr2(B) ** 2 - det2(B)) * B[i][j] - tr2(B) * det2(B) * (1 if i == j else 0)
        assert tr2(B2) == tr2(B) ** 2 - 2 * det2(B)
    hyps = "(ht : Matrix.trace A = %s) (hd : Matrix.det A = %s)" % (zn(t), zn(d))
    words = "Let \\(A\\) be a \\(2 \\times 2\\) integer matrix with trace %d and determinant %d. " % (t, d)
    if kind == "cayley":
        stmt = "(A : %s) %s :\n    A ^ 2 = %s • A - %s • (1 : %s)" % (M2, hyps, zn(t), zn(d), M2)
        proof = ("by\n  have key : A ^ 2 = Matrix.trace A • A - Matrix.det A • (1 : %s) := by\n    rw [Matrix.eta_fin_two A, Matrix.one_fin_two, pow_two, Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]\n"
                 "    ext i j\n    fin_cases i <;> fin_cases j <;> simp <;> ring\n  rw [key, ht, hd]") % M2
        return words + "Then \\(A^2 = %d A - %d I\\), where \\(I\\) is the identity matrix." % (t, d), [Theorem("square_of_matrix", stmt, proof, "A^2 = tr(A) A - det(A) I with the given trace and determinant.")]
    if kind == "cayley3":
        stmt = "(A : %s) %s :\n    A ^ 3 = %s • A - %s • (1 : %s)" % (M2, hyps, zn(t * t - d), zn(t * d), M2)
        proof = ("by\n  have h2 := cayley_hamilton_two A\n  rw [ht, hd] at h2\n  calc A ^ 3 = A * A ^ 2 := by rw [pow_succ']\n    _ = A * (%s • A - %s • (1 : %s)) := by rw [h2]\n"
                 "    _ = %s • (A * A) - %s • A := by simp only [mul_sub, mul_smul_comm, mul_one]\n    _ = %s • (%s • A - %s • (1 : %s)) - %s • A := by rw [← pow_two, h2]\n"
                 "    _ = %s • A - %s • (1 : %s) := by module") % (zn(t), zn(d), M2, zn(t), zn(d), zn(t), zn(t), zn(d), M2, zn(d), zn(t * t - d), zn(t * d), M2)
        main = Theorem("cube_of_matrix", stmt, proof, "A^3 in terms of the trace and determinant.", 0.6)
        return words + "Then \\(A^3 = %d A - %d I\\), where \\(I\\) is the identity matrix. You may first prove \\(A^2 = (\\operatorname{tr} A) A - (\\det A) I\\) for every \\(2 \\times 2\\) integer matrix." % (t * t - d, t * d), [CAYLEY, main]
    stmt = "(A : %s) %s :\n    Matrix.trace (A ^ 2) = %s" % (M2, hyps, num(t * t - 2 * d))
    proof = "by\n  rw [cayley_hamilton_two A, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, ht, hd]\n  norm_num"
    main = Theorem("trace_of_square", stmt, proof, "The trace of A^2 from the trace and determinant of A.", 0.6)
    return words + "Then the trace of \\(A^2\\) is %d. You may first prove \\(A^2 = (\\operatorname{tr} A) A - (\\det A) I\\) for every \\(2 \\times 2\\) integer matrix." % (t * t - 2 * d), [CAYLEY, main]

# ---------------------------------------------------------------- matrix_pow

def matrix_pow(rng, difficulty):
    kind = rng.choice({1: ["shear", "shear", "lower"], 2: ["diag", "jordan", "shear2"], 3: ["affine", "shearprod", "affine"]}[difficulty])
    ind = "by\n  induction n with\n  | zero =>\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp\n  | succ j ih =>\n    rw [pow_succ, ih, Matrix.mul_fin_two]\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp <;> ring"
    def check(A, form, extra=lambda n: n):
        P = [[1, 0], [0, 1]]
        for n in range(7):
            assert P == form(n), (A, n, P, form(n))
            P = mm(P, A)
    if kind == "shear":
        k = rng.choice([1, 2, 3, 4, 5, 7, -1, -2, -3])
        check([[1, k], [0, 1]], lambda n: [[1, n * k], [0, 1]])
        stmt = "(n : ℕ) :\n    (!![1, %s; 0, 1] : %s) ^ n = !![1, (n : ℤ) * %s; 0, 1]" % (k, M2, num(k))
        informal = "For every natural number \\(n\\), \\[\\begin{pmatrix} 1 & %d \\\\ 0 & 1 \\end{pmatrix}^n = \\begin{pmatrix} 1 & %dn \\\\ 0 & 1 \\end{pmatrix}.\\]" % (k, k)
        return informal, [Theorem("shear_power", stmt, ind, "Powers of a shear matrix.")]
    if kind == "lower":
        k = rng.choice([1, 2, 3, 4, 5, 6, -1, -2, -4])
        check([[1, 0], [k, 1]], lambda n: [[1, 0], [n * k, 1]])
        stmt = "(n : ℕ) :\n    (!![1, 0; %s, 1] : %s) ^ n = !![1, 0; (n : ℤ) * %s, 1]" % (k, M2, num(k))
        informal = "For every natural number \\(n\\), \\[\\begin{pmatrix} 1 & 0 \\\\ %d & 1 \\end{pmatrix}^n = \\begin{pmatrix} 1 & 0 \\\\ %dn & 1 \\end{pmatrix}.\\]" % (k, k)
        return informal, [Theorem("lower_shear_power", stmt, ind, "Powers of a lower shear matrix.")]
    if kind == "diag":
        p, q = rng.sample([2, 3, 4, 5, -2, -3, 6, 7], 2)
        check([[p, 0], [0, q]], lambda n: [[p ** n, 0], [0, q ** n]])
        stmt = "(n : ℕ) :\n    (!![%s, 0; 0, %s] : %s) ^ n = !![%s ^ n, 0; 0, %s ^ n]" % (num(p), num(q), M2, num(p), num(q))
        informal = "For every natural number \\(n\\), \\[\\begin{pmatrix} %d & 0 \\\\ 0 & %d \\end{pmatrix}^n = \\begin{pmatrix} (%d)^n & 0 \\\\ 0 & (%d)^n \\end{pmatrix}.\\]" % (p, q, p, q)
        return informal, [Theorem("diagonal_power", stmt, ind, "Powers of a diagonal matrix.")]
    if kind == "jordan":
        p = rng.choice([2, 3, 4, 5, -2, -3, 6])
        check([[p, 1], [0, p]], lambda n: [[p ** n, n * p ** (n - 1) if n else 0], [0, p ** n]])
        stmt = "(n : ℕ) :\n    (!![%s, 1; 0, %s] : %s) ^ (n + 1) = !![%s ^ (n + 1), ((n : ℤ) + 1) * %s ^ n; 0, %s ^ (n + 1)]" % (num(p), num(p), M2, num(p), num(p), num(p))
        proof = "by\n  induction n with\n  | zero =>\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp\n  | succ j ih =>\n    rw [pow_succ, ih, Matrix.mul_fin_two]\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp [pow_succ] <;> ring"
        informal = "For every natural number \\(n\\), \\[\\begin{pmatrix} %d & 1 \\\\ 0 & %d \\end{pmatrix}^{n+1} = \\begin{pmatrix} (%d)^{n+1} & (n+1)(%d)^n \\\\ 0 & (%d)^{n+1} \\end{pmatrix}.\\]" % (p, p, p, p, p)
        return informal, [Theorem("jordan_power", stmt, proof, "Powers of a 2x2 Jordan block.")]
    if kind == "shear2":
        k, l = rng.sample([1, 2, 3, 4, 5, -1, -2], 2)
        check([[1, k], [l * 0, 1]], lambda n: [[1, n * k], [0, 1]])
        a = rng.choice([2, 3, 4, 5]); b = rng.choice([1, 2, 3, 4, 5, 6])
        # (diag(1,1) shear)^n times a scalar: (a * S)^n = a^n * S^n
        stmt = "(n : ℕ) :\n    (!![%d, %d; 0, %d] : %s) ^ n = !![(%d : ℤ) ^ n, (n : ℤ) * %d * %d ^ (n - 1); 0, (%d : ℤ) ^ n]" % (a, a * k, a, M2, a, a * k, a, a) if False else None
        # an exact variant: lower triangular with equal diagonal: !![a, 0; 1, a]^(n+1)
        check([[a, 0], [1, a]], lambda n: [[a ** n, 0], [n * a ** (n - 1) if n else 0, a ** n]])
        stmt = "(n : ℕ) :\n    (!![%d, 0; 1, %d] : %s) ^ (n + 1) = !![(%d : ℤ) ^ (n + 1), 0; ((n : ℤ) + 1) * %d ^ n, (%d : ℤ) ^ (n + 1)]" % (a, a, M2, a, a, a)
        proof = "by\n  induction n with\n  | zero =>\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp\n  | succ j ih =>\n    rw [pow_succ, ih, Matrix.mul_fin_two]\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp [pow_succ] <;> ring"
        informal = "For every natural number \\(n\\), \\[\\begin{pmatrix} %d & 0 \\\\ 1 & %d \\end{pmatrix}^{n+1} = \\begin{pmatrix} %d^{n+1} & 0 \\\\ (n+1)\\,%d^{n} & %d^{n+1} \\end{pmatrix}.\\]" % (a, a, a, a, a)
        return informal, [Theorem("lower_jordan_power", stmt, proof, "Powers of a lower 2x2 Jordan block.")]
    if kind == "affine":
        a = rng.choice([2, 3, 4, 5, -2, -3]); b = rng.choice([1, 2, 3, 4, 5, 6, -1, -2])
        check([[a, b], [0, 1]], lambda n: [[a ** n, b * sum(a ** i for i in range(n))], [0, 1]])
        stmt = "(n : ℕ) :\n    (!![%s, %s; 0, 1] : %s) ^ n = !![%s ^ n, %s * ∑ i ∈ Finset.range n, %s ^ i; 0, 1]" % (num(a), num(b), M2, num(a), num(b), num(a))
        proof = "by\n  induction n with\n  | zero =>\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp\n  | succ j ih =>\n    rw [pow_succ, ih, Matrix.mul_fin_two]\n    ext i j\n    fin_cases i <;> fin_cases j <;> simp [Finset.sum_range_succ, pow_succ] <;> ring"
        informal = "For every natural number \\(n\\), \\[\\begin{pmatrix} %d & %d \\\\ 0 & 1 \\end{pmatrix}^n = \\begin{pmatrix} (%d)^n & %d \\sum_{i=0}^{n-1} (%d)^i \\\\ 0 & 1 \\end{pmatrix}.\\] The sum is empty when \\(n = 0\\)." % (a, b, a, b, a)
        return informal, [Theorem("affine_power", stmt, proof, "Powers of an affine map matrix, with a geometric sum.")]
    k, l = rng.sample([1, 2, 3, 4, 5, 6, -1, -2, -3], 2)
    for n in range(5):
        for m in range(5): assert mm([[1, n * k], [0, 1]], [[1, m * l], [0, 1]]) == [[1, n * k + m * l], [0, 1]]
    lem = Theorem("shear_power", "(k : ℤ) (n : ℕ) :\n    (!![1, k; 0, 1] : %s) ^ n = !![1, (n : ℤ) * k; 0, 1]" % M2, ind, "Powers of a shear matrix.", 0.4)
    main = Theorem("shear_product", "(n m : ℕ) :\n    (!![1, %s; 0, 1] : %s) ^ n * (!![1, %s; 0, 1] : %s) ^ m = !![1, (n : ℤ) * %s + (m : ℤ) * %s; 0, 1]" % (num(k), M2, num(l), M2, num(k), num(l)),
                   "by\n  rw [shear_power, shear_power, Matrix.mul_fin_two]\n  ext i j\n  fin_cases i <;> fin_cases j <;> simp <;> ring", "A product of powers of two shears.", 0.6)
    informal = ("For every integer \\(k\\) and natural number \\(n\\), \\[\\begin{pmatrix} 1 & k \\\\ 0 & 1 \\end{pmatrix}^n = \\begin{pmatrix} 1 & nk \\\\ 0 & 1 \\end{pmatrix}.\\] "
                "Deduce that for all natural numbers \\(n, m\\), \\[\\begin{pmatrix} 1 & %d \\\\ 0 & 1 \\end{pmatrix}^n \\begin{pmatrix} 1 & %d \\\\ 0 & 1 \\end{pmatrix}^m = \\begin{pmatrix} 1 & %dn + %dm \\\\ 0 & 1 \\end{pmatrix}.\\]" % (k, l, k, l))
    return informal, [lem, main]

# ---------------------------------------------------------------- independence

def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0]) + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

def rank_frac(rows):
    A = [[F(x) for x in r] for r in rows]; rank = 0
    for c in range(len(A[0])):
        piv = next((r for r in range(rank, len(A)) if A[r][c] != 0), None)
        if piv is None: continue
        A[rank], A[piv] = A[piv], A[rank]
        for r in range(len(A)):
            if r != rank and A[r][c] != 0:
                f = A[r][c] / A[rank][c]; A[r] = [x - f * y for x, y in zip(A[r], A[rank])]
        rank += 1
    return rank

def vec(v, n): return "(![%s] : Fin %d → ℚ)" % (", ".join(str(x) for x in v), n)
def vecs(vs, n): return "![%s, %s]" % (vec(vs[0], n), ", ".join("![%s]" % ", ".join(str(x) for x in v) for v in vs[1:]))
def tv(v): return "\\begin{pmatrix} %s \\end{pmatrix}" % " \\\\ ".join(str(x) for x in v)

def independence(rng, difficulty):
    n = 2 if difficulty < 3 else 3
    dependent = rng.random() < (0.35 if difficulty == 1 else 0.5)
    r = 4 if difficulty == 1 else 6
    while True:
        vs = [[rng.randrange(-r, r + 1) for _ in range(n)] for _ in range(n)]
        if any(all(x == 0 for x in v) for v in vs): continue
        if dependent:
            coef = [rng.choice([-3, -2, -1, 1, 2, 3]) for _ in range(n - 1)]
            vs[-1] = [sum(c * vs[i][j] for i, c in enumerate(coef)) for j in range(n)]
            if all(x == 0 for x in vs[-1]) or rank_frac(vs) != n - 1: continue
            break
        if rank_frac(vs) == n and (det3(vs) if n == 3 else det2(vs)) != 0: break
    assert (rank_frac(vs) == n) == (not dependent)
    S = vecs(vs, n)
    names = "two" if n == 2 else "three"
    informal = "In \\(\\mathbb{Q}^%d\\) consider the vectors %s. " % (n, ", ".join("\\(%s\\)" % tv(v) for v in vs))
    if not dependent:
        informal += "Show that they are linearly independent over \\(\\mathbb{Q}\\)."
        if n == 2:
            proof = ("by\n  rw [LinearIndependent.pair_iff]\n  intro s t h\n  have h0 := congr_fun h 0\n  have h1 := congr_fun h 1\n  simp at h0 h1\n  constructor <;> linarith")
        else:
            proof = ("by\n  rw [Fintype.linearIndependent_iff]\n  intro g hg\n  have h0 := congr_fun hg 0\n  have h1 := congr_fun hg 1\n  have h2 := congr_fun hg 2\n"
                     "  simp [Fin.sum_univ_three] at h0 h1 h2\n  intro i\n  fin_cases i <;> simp <;> linarith")
        return informal, [Theorem("vectors_independent", ": LinearIndependent ℚ %s" % S, proof, "The given vectors are linearly independent over the rationals.")]
    informal += "Show that they are not linearly independent over \\(\\mathbb{Q}\\)."
    coefs = coef + [-1]
    gl = "![%s]" % ", ".join("(%d : ℚ)" % c for c in coefs)
    sumfn = "Fin.sum_univ_two" if n == 2 else "Fin.sum_univ_three"
    proof = ("by\n  rw [Fintype.not_linearIndependent_iff]\n  refine ⟨%s, ?_, %d, by simp⟩\n  ext i\n  fin_cases i <;> simp [%s] <;> norm_num") % (gl, n - 1, sumfn)
    return informal, [Theorem("vectors_dependent", ": ¬ LinearIndependent ℚ %s" % S, proof, "The given vectors are linearly dependent over the rationals.")]

# ---------------------------------------------------------------- linear_map

HP = {
    "pt": ("(hp : ∀ x, {p} ({p} x) = {p} x)", "{p}({p}(x)) = {p}(x) for every vector x", "have hp' : ∀ x, {p} ({p} x) = {p} x := hp"),
    "comp": ("(hp : {p} ∘ₗ {p} = {p})", "{p} \\circ {p} = {p}", "have hp' : ∀ x, {p} ({p} x) = {p} x := fun x => LinearMap.congr_fun hp x"),
    "mul": ("(hp : {p} * {p} = {p})", "{p}^2 = {p}", "have hp' : ∀ x, {p} ({p} x) = {p} x := fun x => LinearMap.congr_fun hp x"),
}

def linear_map(rng, difficulty):
    Fd, Ftex = rng.choice([("ℚ", "\\mathbb{Q}"), ("ℝ", "\\mathbb{R}")])
    V, W = "V", "W"; p = rng.choice(["p", "e", "q"]); x, y = rng.choice([("x", "y"), ("u", "v"), ("a", "b")])
    kind = rng.choice({1: ["kercomb", "projsub", "kercomb"], 2: ["kersmul", "rangecomp", "kercomp", "kerid"], 3: ["iscompl", "iscompl", "kerid", "idem"]}[difficulty])
    sp = "{%s %s : Type*} [AddCommGroup %s] [Module %s %s] [AddCommGroup %s] [Module %s %s]" % (V, W, V, Fd, V, W, Fd, W)
    sv = "{%s : Type*} [AddCommGroup %s] [Module %s %s]" % (V, V, Fd, V)
    hpl, hpt, hpf = HP[rng.choice((["comp", "mul"] if kind == "idem" else ["pt", "comp", "mul"]) if difficulty > 1 else ["pt"])]
    if difficulty == 3 and kind in ("kerid", "idem"):
        pass
    key = None
    for k in HP:
        if HP[k][0] == hpl: key = k
    hpl, hpt, hpf = (s.replace("{p}", p) for s in (hpl, hpt, hpf))
    if kind == "kercomb":
        a, b = rng.sample([2, 3, 4, 5, -1, -2, -3, 7], 2)
        stmt = "%s (f : %s →ₗ[%s] %s) {%s %s : %s}\n    (hx : f %s = 0) (hy : f %s = 0) : f ((%d : %s) • %s + (%d : %s) • %s) = 0" % (sp, V, Fd, W, x, y, V, x, y, a, Fd, x, b, Fd, y)
        informal = "Let \\(f : V \\to W\\) be a linear map of vector spaces over \\(%s\\) and \\(%s, %s \\in V\\) with \\(f(%s) = 0\\) and \\(f(%s) = 0\\). Then \\(f(%d%s + %d%s) = 0\\)." % (Ftex, x, y, x, y, a, x, b, y)
        return informal, [Theorem("kernel_combination", stmt, "by\n  rw [map_add, map_smul, map_smul, hx, hy]\n  simp", "The kernel is closed under linear combinations.")]
    if kind == "projsub":
        stmt = "%s (%s : %s →ₗ[%s] %s) (hp : ∀ x, %s (%s x) = %s x) (%s : %s) :\n    %s - %s %s ∈ LinearMap.ker %s" % (sv, p, V, Fd, V, p, p, p, x, V, x, p, x, p)
        informal = "Let \\(%s : V \\to V\\) be a linear map over \\(%s\\) with \\(%s(%s(v)) = %s(v)\\) for every \\(v\\). Then \\(%s - %s(%s)\\) lies in the kernel of \\(%s\\) for every \\(%s \\in V\\)." % (p, Ftex, p, "v", "v", x, p, x, p, x)
        return informal, [Theorem("sub_proj_mem_ker", stmt, "by\n  rw [LinearMap.mem_ker, map_sub, hp, sub_self]", "x - p x lies in the kernel of an idempotent map p.")]
    if kind == "kersmul":
        c = rng.choice([2, 3, 4, 5, 7, -1, -2, -3])
        stmt = "%s (f : %s →ₗ[%s] %s) :\n    LinearMap.ker ((%d : %s) • f) = LinearMap.ker f" % (sp, V, Fd, W, c, Fd)
        informal = "Let \\(f : V \\to W\\) be a linear map of vector spaces over \\(%s\\). Then the kernel of \\(%df\\) equals the kernel of \\(f\\)." % (Ftex, c)
        proof = "by\n  ext %s\n  simp only [LinearMap.mem_ker, LinearMap.smul_apply, smul_eq_zero]\n  constructor\n  · rintro (h | h)\n    · norm_num at h\n    · exact h\n  · intro h\n    exact Or.inr h" % x
        return informal, [Theorem("ker_smul_eq", stmt, proof, "A nonzero scalar multiple has the same kernel.")]
    if kind in ("rangecomp", "kercomp"):
        U = "U"
        pre = "{%s %s %s : Type*} [AddCommGroup %s] [Module %s %s] [AddCommGroup %s] [Module %s %s] [AddCommGroup %s] [Module %s %s]" % (V, W, U, V, Fd, V, W, Fd, W, U, Fd, U)
        if kind == "rangecomp":
            stmt = "%s (f : %s →ₗ[%s] %s) (g : %s →ₗ[%s] %s) :\n    LinearMap.range (g ∘ₗ f) ≤ LinearMap.range g" % (pre, V, Fd, W, W, Fd, U)
            informal = "Let \\(f : V \\to W\\) and \\(g : W \\to U\\) be linear maps over \\(%s\\). Then the range of \\(g \\circ f\\) is contained in the range of \\(g\\)." % Ftex
            proof = "by\n  rintro z ⟨%s, rfl⟩\n  exact ⟨f %s, rfl⟩" % (x, x)
            return informal, [Theorem("range_comp_le", stmt, proof, "range (g ∘ f) ≤ range g.")]
        stmt = "%s (f : %s →ₗ[%s] %s) (g : %s →ₗ[%s] %s) :\n    LinearMap.ker f ≤ LinearMap.ker (g ∘ₗ f)" % (pre, V, Fd, W, W, Fd, U)
        informal = "Let \\(f : V \\to W\\) and \\(g : W \\to U\\) be linear maps over \\(%s\\). Then the kernel of \\(f\\) is contained in the kernel of \\(g \\circ f\\)." % Ftex
        proof = "by\n  intro %s hx\n  rw [LinearMap.mem_ker] at hx ⊢\n  rw [LinearMap.comp_apply, hx, map_zero]" % x
        return informal, [Theorem("ker_le_comp", stmt, proof, "ker f ≤ ker (g ∘ f).")]
    if kind == "idem":
        stmt = "%s (%s : %s →ₗ[%s] %s) %s :\n    (LinearMap.id - %s) ∘ₗ (LinearMap.id - %s) = LinearMap.id - %s ∧ %s ∘ₗ (LinearMap.id - %s) = 0" % (sv, p, V, Fd, V, hpl, p, p, p, p, p)
        informal = "Let \\(%s : V \\to V\\) be a linear map over \\(%s\\) with \\(%s\\). Then \\(\\mathrm{id} - %s\\) is also idempotent, and \\(%s \\circ (\\mathrm{id} - %s) = 0\\)." % (p, Ftex, hpt, p, p, p)
        proof = "by\n  %s\n  refine ⟨?_, ?_⟩ <;> ext %s <;> simp [hp']" % (hpf, x)
        return informal, [Theorem("complement_idempotent", stmt, proof, "If p is idempotent then so is id - p, and p kills its image.")]
    if kind == "kerid":
        stmt = "%s (%s : %s →ₗ[%s] %s) %s :\n    LinearMap.ker (LinearMap.id - %s) = LinearMap.range %s" % (sv, p, V, Fd, V, hpl, p, p)
        informal = "Let \\(%s : V \\to V\\) be a linear map over \\(%s\\) with \\(%s\\). Then the kernel of \\(\\mathrm{id} - %s\\) equals the range of \\(%s\\)." % (p, Ftex, hpt, p, p)
        proof = ("by\n  %s\n  ext %s\n  constructor\n  · intro h\n    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h\n    exact ⟨%s, h.symm⟩\n"
                 "  · rintro ⟨%s, rfl⟩\n    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hp', sub_self]") % (hpf, x, x, y)
        return informal, [Theorem("ker_id_sub", stmt, proof, "For idempotent p, the kernel of id - p is the range of p.")]
    # iscompl
    stmt0 = "%s (%s : %s →ₗ[%s] %s) %s" % (sv, p, V, Fd, V, hpl)
    lem = Theorem("disjoint_ker_range", stmt0 + " :\n    Disjoint (LinearMap.ker %s) (LinearMap.range %s)" % (p, p),
                  "by\n  %s\n  rw [Submodule.disjoint_def]\n  rintro %s h1 ⟨%s, rfl⟩\n  rw [LinearMap.mem_ker, hp'] at h1\n  rw [h1]" % (hpf, x, y), "The kernel and the range of an idempotent map meet only in 0.", 0.4)
    main = Theorem("ker_range_isCompl", stmt0 + " :\n    IsCompl (LinearMap.ker %s) (LinearMap.range %s)" % (p, p),
                   ("by\n  %s\n  refine ⟨disjoint_ker_range %s hp, ?_⟩\n  rw [codisjoint_iff, eq_top_iff]\n  intro %s _\n  rw [Submodule.mem_sup]\n"
                    "  exact ⟨%s - %s %s, by rw [LinearMap.mem_ker, map_sub, hp', sub_self], %s %s, LinearMap.mem_range_self %s %s, by abel⟩") % (hpf, p, x, x, p, x, p, x, p, x),
                   "The kernel and the range of an idempotent map are complements.", 0.6)
    informal = "Let \\(%s : V \\to V\\) be a linear map over \\(%s\\) with \\(%s\\). Show that \\(\\ker %s\\) and \\(\\operatorname{range} %s\\) are complementary subspaces: their intersection is \\(\\{0\\}\\) and together they span \\(V\\)." % (p, Ftex, hpt, p, p)
    return informal, [lem, main]

FAM = {"det_trace": det_trace, "matrix_pow": matrix_pow, "independence": independence, "linear_map": linear_map}
TITLES = {"det_trace": "Determinant and trace of 2x2 matrices", "matrix_pow": "Powers of 2x2 matrices", "independence": "Linear independence of explicit vectors", "linear_map": "Kernels, ranges and projections"}

def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    informal, theorems = FAM[family](rng, difficulty)
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove",
        title=TITLES[family], informal="Prove the following statement.\n\n" + informal, theorems=theorems)
