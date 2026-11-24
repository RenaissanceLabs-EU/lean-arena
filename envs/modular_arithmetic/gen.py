"""Divisibility, congruences, parity and coprimality (MSC 11: number theory, 11A07 congruences, 11A05 gcd).

Families:
  power_residues    residues of u*n^k + w (one variable) or non-attained residues of u*a^k + v*b^k + w;
  divisibility      m | a*n^p + b*n over the integers (Fermat-style p-th powers), proved in ZMod;
  congruence_chain  from x = r (mod m) derive a congruence for a polynomial in x (Int.ModEq);
  gcd_coprime       coprimality of two linear forms and their gcd.
Second code path: every residue set, every divisibility claim, every congruence value and every gcd
claim is recomputed by brute force in Python before the task is returned.
"""
from math import gcd
from arena.core import Task, Theorem, rng_for

ENV = "modular_arithmetic"
FAMILIES = ["congruence_chain", "divisibility", "gcd_coprime", "power_residues"]

PRIMES_FOR = {2: [2], 3: [2, 3], 5: [2, 3, 5], 7: [2, 3, 7]}   # primes q with n^p = n (mod q)


def poly(terms, tex=False):
    """terms: list of (coef, lean monomial, tex monomial); '' means the constant term."""
    out = ""
    for i, (c, lm, tm) in enumerate(terms):
        m = tm if tex else lm
        mag = abs(c)
        if m == "": body = "%d" % mag
        elif mag == 1: body = m
        elif tex: body = "%d%s" % (mag, m)
        else: body = "%d * %s" % (mag, m)
        if i == 0: out += ("-" if c < 0 else "") + body
        else: out += (" - " if c < 0 else " + ") + body
    return out


def ml(proof, c):
    """ModEq proof of c * (...) from a proof of (...), skipping the factor 1."""
    return proof if c == 1 else "(%s).mul_left %d" % (proof, c)


def mono(c, body):
    return body if c == 1 else "%d * %s" % (c, body)


def paren(c):
    return "(%d)" % c if c < 0 else "%d" % c


# ---------------------------------------------------------------- power_residues
def power_residues(rng, difficulty):
    if difficulty < 3:
        while True:
            m = rng.choice([3, 4, 5, 7, 8, 9] if difficulty == 1 else [5, 7, 9, 11, 13, 16])
            k = 2 if difficulty == 1 else rng.choice([3, 4])
            u = rng.randrange(1, m); w = rng.randrange(0, m)
            res = sorted({(u * x ** k + w) % m for x in range(m)})
            free = {(u * x + w) % m for x in range(m)}          # residues if n^k were an arbitrary number
            if 2 <= len(res) and len(res) < len(free): break
        # second path: the residues over a long range of n agree with the residues over one period
        assert sorted({(u * n ** k + w) % m for n in range(5 * m + 3)}) == res
        expr = poly([(u, "n ^ %d" % k, "n^%d" % k)] + ([(w, "", "")] if w else []))
        texexpr = poly([(u, "n ^ %d" % k, "n^%d" % k)] + ([(w, "", "")] if w else []), tex=True)
        cases = " ∨ ".join("(%s) %% %d = %d" % (expr, m, r) for r in res)
        tex = ", ".join("%d" % r for r in res)
        informal = ("Prove that for every natural number \\(n\\), the remainder of \\(%s\\) on division by \\(%d\\) is one of \\(%s\\)."
                    % (texexpr, m, tex))
        stmt = "(n : ℕ) :\n    %s" % cases
        proof = ("by\n  have key : (%s) %% %d = (%s) %% %d :=\n    (%s).add_right %d\n"
                 "  have h := Nat.mod_lt n (show 0 < %d by norm_num)\n  rw [key]\n  generalize n %% %d = r at h ⊢\n  interval_cases r <;> decide"
                 % (expr, m, mono(u, "(n %% %d) ^ %d" % (m, k)) + " + %d" % w, m, ml("((Nat.mod_modEq n %d).symm.pow %d)" % (m, k), u), w, m, m))
        return informal, [Theorem("residues_of_power", stmt, proof, "The remainder of the expression is one of the listed values.")]
    while True:
        m = rng.choice([4, 5, 7, 8, 9]); k = rng.choice([2, 3])
        u = rng.randrange(1, 4); v = rng.randrange(1, 4); w = rng.randrange(0, m)
        got = {(u * a ** k + v * b ** k + w) % m for a in range(m) for b in range(m)}
        free = {(u * x + v * y + w) % m for x in range(m) for y in range(m)}   # if the powers were arbitrary numbers
        missing = [r for r in range(m) if r not in got and r in free]
        if missing: break
    r = rng.choice(missing)
    for a in range(2 * m + 2):
        for b in range(2 * m + 2): assert (u * a ** k + v * b ** k + w) % m != r
    expr = poly([(u, "a ^ %d" % k, "a^%d" % k), (v, "b ^ %d" % k, "b^%d" % k)] + ([(w, "", "")] if w else []))
    texexpr = poly([(u, "a^%d" % k, "a^%d" % k), (v, "b^%d" % k, "b^%d" % k)] + ([(w, "", "")] if w else []), tex=True)
    informal = "Prove that for all natural numbers \\(a\\) and \\(b\\), the number \\(%s\\) never leaves remainder \\(%d\\) on division by \\(%d\\)." % (texexpr, r, m)
    stmt = "(a b : ℕ) :\n    (%s) %% %d ≠ %d" % (expr, m, r)
    sub = "%s + %s + %d" % (mono(u, "(a %% %d) ^ %d" % (m, k)), mono(v, "(b %% %d) ^ %d" % (m, k)), w)
    proof = ("by\n  have key : (%s) %% %d = (%s) %% %d :=\n"
             "    ((%s).add (%s)).add_right %d\n"
             "  have ha := Nat.mod_lt a (show 0 < %d by norm_num)\n  have hb := Nat.mod_lt b (show 0 < %d by norm_num)\n  rw [key]\n"
             "  generalize a %% %d = x at ha ⊢\n  generalize b %% %d = y at hb ⊢\n  interval_cases x <;> interval_cases y <;> decide"
             % (expr, m, sub, m, ml("((Nat.mod_modEq a %d).symm.pow %d)" % (m, k), u), ml("((Nat.mod_modEq b %d).symm.pow %d)" % (m, k), v), w, m, m, m, m))
    return informal, [Theorem("residue_never_attained", stmt, proof, "The expression never leaves the stated remainder.")]


# ---------------------------------------------------------------- divisibility
def zmod_proof(M, expr):
    return ("by\n  have h : ((%s : ℤ) : ZMod %d) = 0 := by\n    push_cast\n    generalize (n : ZMod %d) = x\n    revert x\n    decide +kernel\n"
            "  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h" % (expr, M, M))


def divisibility(rng, difficulty):
    if difficulty == 1:
        p = rng.choice([3, 5, 7]); ps = PRIMES_FOR[p]
        sub = [q for q in ps if rng.random() < 0.6] or [rng.choice(ps)]
        M = 1
        for q in sub: M *= q
    else:
        p = rng.choice([3, 5, 7] if difficulty == 2 else [5, 7]); ps = PRIMES_FOR[p]
        M = 1
        for q in ps: M *= q
    while True:
        a = rng.randrange(1, 41); t = rng.randrange(-3, 4); b = M * t - a
        if b != 0 and gcd(a, M) == 1: break
    for n in range(-60, 61): assert (a * n ** p + b * n) % M == 0
    terms = [(a, "n ^ %d" % p, "n^%d" % p), (b, "n", "n")]
    expr = poly(terms); texexpr = poly(terms, tex=True)
    informal = "Prove that for every integer \\(n\\), the number \\(%d\\) divides \\(%s\\)." % (M, texexpr)
    if difficulty < 3:
        stmt = "(n : ℤ) :\n    (%d : ℤ) ∣ %s" % (M, expr)
        return informal, [Theorem("dvd_poly", stmt, zmod_proof(M, expr), "The integer divides the polynomial value.")]
    ths = []
    for q in ps:
        ths.append(Theorem("dvd_by_%d" % q, "(n : ℤ) :\n    (%d : ℤ) ∣ %s" % (q, expr), zmod_proof(q, expr),
                           "The prime %d divides the polynomial value." % q))
    haves = "\n".join("  have h%d := dvd_by_%d n" % (q, q) for q in ps)
    main = Theorem("dvd_poly", "(n : ℤ) :\n    (%d : ℤ) ∣ %s" % (M, expr), "by\n%s\n  generalize %s = e at %s ⊢\n  omega" % (haves, expr, " ".join("h%d" % q for q in ps)),
                   "The product of the primes divides the polynomial value.", weight=float(len(ps)))
    return informal + " Prove it first for each prime factor of \\(%d\\), then combine." % M, ths + [main]


# ---------------------------------------------------------------- congruence_chain
def congruence_chain(rng, difficulty):
    m = rng.randrange(5, 14)
    if difficulty == 1:
        r = rng.randrange(0, m); u, v, w = rng.randrange(1, 8), rng.randrange(1, 8), rng.randrange(1, 8)
        val = (u * r * r + v * r + w) % m
        for x in range(-3 * m, 3 * m):
            if x % m == r: assert (u * x * x + v * x + w - val) % m == 0
        terms = [(u, "x ^ 2", "x^2"), (v, "x", "x"), (w, "", "")]
        expr = poly(terms); tex = poly(terms, tex=True)
        informal = "Let \\(x\\) be an integer with \\(x \\equiv %d \\pmod{%d}\\). Prove that \\(%s \\equiv %d \\pmod{%d}\\)." % (r, m, tex, val, m)
        stmt = "(x : ℤ) (h : x ≡ %d [ZMOD %d]) :\n    %s ≡ %d [ZMOD %d]" % (r, m, expr, val, m)
        proof = ("by\n  have h1 := ((%s).add (%s)).add_right %d\n  refine h1.trans ?_\n  norm_num [Int.ModEq]" % (ml("h.pow 2", u), ml("h", v), w))
        return informal, [Theorem("congr_poly", stmt, proof, "The polynomial is congruent to the stated residue.")]
    if difficulty == 2:
        r, s = rng.randrange(0, m), rng.randrange(0, m)
        u, v, w = rng.randrange(1, 8), rng.randrange(1, 8), rng.randrange(1, 8)
        val = (u * r * s + v * s * s + w * r) % m
        for x in range(-2 * m, 2 * m, 3):
            for y in range(-2 * m, 2 * m, 5):
                if x % m == r and y % m == s: assert (u * x * y + v * y * y + w * x - val) % m == 0
        terms = [(u, "x * y", "xy"), (v, "y ^ 2", "y^2"), (w, "x", "x")]
        expr = mono(u, "(x * y)") + " + " + mono(v, "y ^ 2") + " + " + mono(w, "x"); tex = poly(terms, tex=True)
        informal = "Let \\(x\\) and \\(y\\) be integers with \\(x \\equiv %d \\pmod{%d}\\) and \\(y \\equiv %d \\pmod{%d}\\). Prove that \\(%s \\equiv %d \\pmod{%d}\\)." % (r, m, s, m, tex, val, m)
        stmt = "(x y : ℤ) (hx : x ≡ %d [ZMOD %d]) (hy : y ≡ %d [ZMOD %d]) :\n    %s ≡ %d [ZMOD %d]" % (r, m, s, m, expr, val, m)
        proof = ("by\n  have h1 := ((%s).add (%s)).add (%s)\n  refine h1.trans ?_\n  norm_num [Int.ModEq]" % (ml("hx.mul hy", u), ml("hy.pow 2", v), ml("hx", w)))
        return informal, [Theorem("congr_poly2", stmt, proof, "The expression is congruent to the stated residue.")]
    m = rng.randrange(7, 14)
    r, s = rng.randrange(2, m), rng.randrange(2, m)
    e, f = rng.randrange(8, 40), rng.randrange(8, 40); w = rng.randrange(1, 9)
    ve, vf = pow(r, e, m), pow(s, f, m)
    val = (ve * vf + w) % m
    for x in (r, r + m, r - 2 * m):
        for y in (s, s + 3 * m, s - m): assert (x ** e * y ** f + w - val) % m == 0
    informal = ("Let \\(x\\) and \\(y\\) be integers with \\(x \\equiv %d \\pmod{%d}\\) and \\(y \\equiv %d \\pmod{%d}\\). "
                "Prove that \\(x^{%d} \\equiv %d \\pmod{%d}\\), and then that \\(x^{%d} y^{%d} + %d \\equiv %d \\pmod{%d}\\)."
                % (r, m, s, m, e, ve, m, e, f, w, val, m))
    lemma = Theorem("congr_pow", "(x : ℤ) (h : x ≡ %d [ZMOD %d]) :\n    x ^ %d ≡ %d [ZMOD %d]" % (r, m, e, ve, m),
                    "by\n  refine (h.pow %d).trans ?_\n  norm_num [Int.ModEq]" % e, "A large power of x has the stated residue.")
    main = Theorem("congr_product", "(x y : ℤ) (hx : x ≡ %d [ZMOD %d]) (hy : y ≡ %d [ZMOD %d]) :\n    x ^ %d * y ^ %d + %d ≡ %d [ZMOD %d]" % (r, m, s, m, e, f, w, val, m),
                   "by\n  have h1 := congr_pow x hx\n  have h2 : y ^ %d ≡ %d [ZMOD %d] := by\n    refine (hy.pow %d).trans ?_\n    norm_num [Int.ModEq]\n"
                   "  refine ((h1.mul h2).add_right %d).trans ?_\n  norm_num [Int.ModEq]" % (f, vf, m, f, w),
                   "The combined expression has the stated residue.", weight=2.0)
    return informal, [lemma, main]


# ---------------------------------------------------------------- gcd_coprime
def linear_pair(rng, want_prime_det):
    while True:
        a, b, c = rng.randrange(1, 10), rng.randrange(1, 10), rng.randrange(1, 10)
        if want_prime_det:
            d = rng.randrange(1, 10)
            D = abs(a * d - b * c)
            if D in (2, 3, 5, 7, 11, 13): return a, b, c, d, a * d - b * c
        else:
            s = rng.choice([1, -1])
            if (b * c + s) % a == 0 and (b * c + s) // a >= 1:
                d = (b * c + s) // a
                return a, b, c, d, a * d - b * c


def gcd_coprime(rng, difficulty):
    a, b, c, d, det = linear_pair(rng, difficulty == 3)
    A = poly([(a, "n", "n"), (b, "", "")]); B = poly([(c, "n", "n"), (d, "", "")])
    tA = poly([(a, "n", "n"), (b, "", "")], tex=True); tB = poly([(c, "n", "n"), (d, "", "")], tex=True)
    if difficulty < 3:
        assert abs(det) == 1 and all(gcd(a * n + b, c * n + d) == 1 for n in range(300))
        s = det
        wit = "⟨%s, %s, by ring⟩" % (paren(-s * c), paren(s * a))
        if difficulty == 1:
            informal = "Prove that for every integer \\(n\\), the integers \\(%s\\) and \\(%s\\) are coprime, in the sense that \\(u(%s) + v(%s) = 1\\) for some integers \\(u, v\\)." % (tA, tB, tA, tB)
            stmt = "(n : ℤ) :\n    IsCoprime (%s) (%s)" % (A, B)
            return informal, [Theorem("coprime_int", stmt, "by\n  exact %s" % wit, "The two linear forms are coprime.")]
        informal = "Prove that for every natural number \\(n\\), the numbers \\(%s\\) and \\(%s\\) are coprime." % (tA, tB)
        stmt = "(n : ℕ) :\n    Nat.Coprime (%s) (%s)" % (A, B)
        proof = "by\n  rw [← Nat.isCoprime_iff_coprime]\n  push_cast\n  exact %s" % wit
        return informal, [Theorem("coprime_nat", stmt, proof, "The two linear forms are coprime.")]
    D = abs(det)
    assert all(D % gcd(a * n + b, c * n + d) == 0 for n in range(300))
    g = "Nat.gcd (%s) (%s)" % (A, B)
    if a * d > b * c: first = "Dvd.dvd.mul_left h2 %d" % a; second = "Dvd.dvd.mul_left h1 %d" % c; e = "%d * (%s) - %d * (%s) = %d" % (a, B, c, A, D)
    else: first = "Dvd.dvd.mul_left h1 %d" % c; second = "Dvd.dvd.mul_left h2 %d" % a; e = "%d * (%s) - %d * (%s) = %d" % (c, A, a, B, D)
    informal = ("Let \\(n\\) be a natural number and \\(g = \\gcd(%s, %s)\\). Prove that \\(g\\) divides \\(%d\\), "
                "and conclude that \\(g = 1\\) or \\(g = %d\\)." % (tA, tB, D, D))
    lemma = Theorem("gcd_dvd_det", "(n : ℕ) :\n    %s ∣ %d" % (g, D),
                    "by\n  have h1 : %s ∣ %s := Nat.gcd_dvd_left _ _\n  have h2 : %s ∣ %s := Nat.gcd_dvd_right _ _\n"
                    "  have h3 := Nat.dvd_sub (%s) (%s)\n  have e : %s := by omega\n  rw [e] at h3\n  exact h3" % (g, A, g, B, first, second, e),
                    "The gcd divides the determinant.")
    main = Theorem("gcd_one_or_prime", "(n : ℕ) :\n    %s = 1 ∨ %s = %d" % (g, g, D),
                   "by\n  exact (Nat.dvd_prime (by norm_num)).1 (gcd_dvd_det n)", "The gcd is 1 or the prime determinant.", weight=2.0)
    return informal, [lemma, main]


def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    informal, theorems = {"power_residues": power_residues, "divisibility": divisibility,
                          "congruence_chain": congruence_chain, "gcd_coprime": gcd_coprime}[family](rng, difficulty)
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove",
                title="Prove a fact about divisibility and residues", informal=informal, theorems=theorems)
