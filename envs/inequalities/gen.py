"""Inequalities over the reals (MSC 26: real functions; 26D05, 26D07, 26D15 inequalities).

Families:
  amgm       AM-GM in two or three variables (squares, field_simp then positivity, a cross-lemma step);
  cauchy     Cauchy-Schwarz small cases, including the bound u x + v y <= w when x^2 + y^2 <= 1;
  abs_ineq   absolute-value inequalities (abs_le, case splits on abs_cases, a product bound);
  monotone   inequalities between values of increasing functions (exp, arctan, sinh, odd powers, sqrt, log).
Second code path: every numeric constant and every inequality is rechecked in Python with exact
fractions (or a float grid for transcendental functions) before the task is returned.
"""
import math
from fractions import Fraction as F
from arena.core import Task, Theorem, rng_for

ENV = "inequalities"
FAMILIES = ["abs_ineq", "amgm", "cauchy", "monotone"]


def mono(c, body):
    return body if c == 1 else "%d * %s" % (c, body)


def tmono(c, body):
    return body if c == 1 else "%d%s" % (c, body)


def sgn_term(c, body, first=False, tex=False):
    """' + c * body' / ' - |c| * body' (or without sign when first)."""
    mag = abs(c)
    b = (body if mag == 1 else ("%d%s" % (mag, body) if tex else "%d * %s" % (mag, body)))
    if first: return ("-" if c < 0 else "") + b
    return (" - " if c < 0 else " + ") + b


def shift(var, c):
    """Lean text of var + c (c an integer)."""
    if c == 0: return var
    return "%s + %d" % (var, c) if c > 0 else "%s - %d" % (var, -c)


def tshift(var, c):
    return shift(var, c)


# ---------------------------------------------------------------- amgm
def amgm(rng, difficulty):
    if difficulty == 1:
        if rng.random() < 0.5:
            p, q = rng.randrange(1, 10), rng.randrange(1, 10)
            K = 4 * p * q
            for a in range(-4, 5):
                for b in range(-4, 5): assert K * a * b <= (p * a + q * b) ** 2
            lhs = "%s * a * b" % K
            pa, qb = mono(p, "a"), mono(q, "b")
            informal = "Prove that for all real numbers \\(a\\) and \\(b\\), \\[%d\\,ab \\le (%s + %s)^2.\\]" % (K, tmono(p, "a"), tmono(q, "b"))
            stmt = "(a b : ℝ) :\n    %s ≤ (%s + %s) ^ 2" % (lhs, pa, qb)
            proof = "by\n  nlinarith [sq_nonneg (%s - %s)]" % (pa, qb)
            return informal, [Theorem("two_var_amgm", stmt, proof, "A square-completion bound for two real numbers.")]
        p, q = rng.randrange(1, 7), rng.randrange(1, 7); s = rng.randrange(1, 41)
        for a in range(-6, 7):
            for b in range(-6, 7):
                if p * a + q * b == s: assert p * q * a * b <= F(s * s, 4)
        pa, qb = mono(p, "a"), mono(q, "b")
        informal = ("Let \\(a\\) and \\(b\\) be real numbers with \\(%s + %s = %d\\). Prove that \\[%s \\le \\frac{%d^2}{4}.\\]"
                    % (tmono(p, "a"), tmono(q, "b"), s, tmono(p * q, "ab"), s))
        stmt = "(a b : ℝ) (h : %s + %s = %d) :\n    %s ≤ %d ^ 2 / 4" % (pa, qb, s, mono(p * q, "a * b"), s)
        proof = ("by\n  have h2 : (%s + %s) ^ 2 = %d ^ 2 := by rw [h]\n  nlinarith [sq_nonneg (%s - %s), h2]" % (pa, qb, s, pa, qb))
        return informal, [Theorem("amgm_constraint", stmt, proof, "The product is at most a quarter of the squared sum.")]
    if difficulty == 2:
        m, u, v = rng.randrange(1, 5), rng.randrange(1, 6), rng.randrange(1, 6)
        k1, k2, T = m * u * u, m * v * v, 2 * m * u * v
        for a in (F(1, 3), F(2), F(7, 5), F(5)):
            for b in (F(1, 2), F(3), F(11, 7), F(1)):
                assert k1 * (a / b) + k2 * (b / a) - T == m * (u * a - v * b) ** 2 / (a * b) >= 0
        if rng.random() < 0.5:
            informal = ("Let \\(a\\) and \\(b\\) be positive real numbers. Prove that \\[%d \\le %s\\frac{a}{b} + %s\\frac{b}{a}.\\]" % (T, tmono(k1, ""), tmono(k2, "")))
            stmt = "(a b : ℝ) (ha : 0 < a) (hb : 0 < b) :\n    %d ≤ %s + %s" % (T, mono(k1, "(a / b)"), mono(k2, "(b / a)"))
            key = "%s + %s - %d = %d * (%s - %s) ^ 2 / (a * b)" % (mono(k1, "(a / b)"), mono(k2, "(b / a)"), T, m, mono(u, "a"), mono(v, "b"))
            proof = ("by\n  have ha' := ha.ne'\n  have hb' := hb.ne'\n  have key : %s := by\n    field_simp\n    ring\n"
                     "  have h : 0 ≤ %d * (%s - %s) ^ 2 / (a * b) := by positivity\n  linarith" % (key, m, mono(u, "a"), mono(v, "b")))
            return informal, [Theorem("amgm_ratio", stmt, proof, "A weighted sum of a ratio and its reciprocal is bounded below.")]
        informal = "Let \\(x\\) be a positive real number. Prove that \\[%d \\le %s + \\frac{%d}{x}.\\]" % (T, tmono(k1, "x"), k2)
        stmt = "(x : ℝ) (hx : 0 < x) :\n    %d ≤ %s + %d / x" % (T, mono(k1, "x"), k2)
        key = "%s + %d / x - %d = %d * (%s - %d) ^ 2 / x" % (mono(k1, "x"), k2, T, m, mono(u, "x"), v)
        proof = ("by\n  have hx' := hx.ne'\n  have key : %s := by\n    field_simp\n    ring\n"
                 "  have h : 0 ≤ %d * (%s - %d) ^ 2 / x := by positivity\n  linarith" % (key, m, mono(u, "x"), v))
        return informal, [Theorem("amgm_linear_plus_inverse", stmt, proof, "The sum of a linear term and an inverse term is bounded below.")]
    p, q, r = rng.randrange(1, 8), rng.randrange(1, 8), rng.randrange(1, 8)
    P = p * q * r
    for a in (F(1), F(2, 3), F(5), F(0)):
        for b in (F(3, 2), F(1, 7), F(4)):
            for c in (F(2), F(9, 4), F(0)):
                assert 27 * P * a * b * c <= (p * a + q * b + r * c) ** 3
    pa, qb, rc = mono(p, "a"), mono(q, "b"), mono(r, "c")
    informal = ("Prove that \\(27xyz \\le (x+y+z)^3\\) for all non-negative real numbers \\(x, y, z\\). "
                "Then prove that for all non-negative real numbers \\(a, b, c\\), \\[%d\\,abc \\le (%s + %s + %s)^3.\\]" % (27 * P, tmono(p, "a"), tmono(q, "b"), tmono(r, "c")))
    hints = ", ".join("mul_nonneg h%s (sq_nonneg (%s - %s))" % (v, w, z) for v, w, z in
                      [("x", "y", "z"), ("y", "z", "x"), ("z", "x", "y"), ("x", "x", "y"), ("x", "x", "z"), ("y", "y", "x"), ("y", "y", "z"), ("z", "z", "x"), ("z", "z", "y")])
    lemma = Theorem("amgm_three", "(x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :\n    27 * x * y * z ≤ (x + y + z) ^ 3",
                    "by\n  nlinarith [%s]" % hints, "The three-variable AM-GM inequality in cubic form.")
    main = Theorem("amgm_three_scaled", "(a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :\n    %d * a * b * c ≤ (%s + %s + %s) ^ 3" % (27 * P, pa, qb, rc),
                   "by\n  have h := amgm_three (%s) (%s) (%s) (by linarith) (by linarith) (by linarith)\n  nlinarith [h]" % (pa, qb, rc),
                   "The scaled three-variable inequality.", weight=2.0)
    return informal, [lemma, main]


# ---------------------------------------------------------------- cauchy
TRIPLES2 = [(3, 4, 5), (5, 12, 13), (8, 15, 17), (7, 24, 25), (20, 21, 29), (6, 8, 10), (9, 12, 15), (12, 16, 20), (15, 8, 17), (12, 5, 13)]
TRIPLES3 = [(1, 2, 2, 3), (2, 3, 6, 7), (1, 4, 8, 9), (4, 4, 7, 9), (2, 6, 9, 11), (6, 6, 7, 11), (3, 4, 12, 13), (2, 10, 11, 15), (1, 12, 12, 17), (4, 8, 8, 12), (2, 2, 1, 3), (6, 2, 3, 7)]


def cauchy(rng, difficulty):
    if difficulty == 1:
        if rng.random() < 0.5:
            p, q = rng.randrange(1, 10), rng.randrange(1, 10); P = p * q
            for a, b, c, d in [(1, 2, 3, 4), (-2, 5, 1, -1), (3, -3, 2, 7)]:
                assert (p * a * c + q * b * d) ** 2 <= (p * a * a + q * b * b) * (p * c * c + q * d * d)
            informal = ("Prove that for all real numbers \\(a, b, c, d\\), \\[(%s + %s)^2 \\le (%s + %s)(%s + %s).\\]"
                        % (tmono(p, "ac"), tmono(q, "bd"), tmono(p, "a^2"), tmono(q, "b^2"), tmono(p, "c^2"), tmono(q, "d^2")))
            stmt = "(a b c d : ℝ) :\n    (%s + %s) ^ 2 ≤ (%s + %s) * (%s + %s)" % (mono(p, "a * c"), mono(q, "b * d"), mono(p, "a ^ 2"), mono(q, "b ^ 2"), mono(p, "c ^ 2"), mono(q, "d ^ 2"))
            proof = "by\n  nlinarith [mul_nonneg (show (0 : ℝ) ≤ %d by norm_num) (sq_nonneg (a * d - b * c))]" % P
            return informal, [Theorem("weighted_cauchy", stmt, proof, "Cauchy-Schwarz with positive weights for two pairs.")]
        p, q = rng.randrange(1, 13), rng.randrange(1, 13); S = p * p + q * q
        for x, y in [(F(1), F(2)), (F(-3), F(5, 2)), (F(0), F(7))]: assert (p * x + q * y) ** 2 <= S * (x * x + y * y)
        informal = "Prove that for all real numbers \\(x\\) and \\(y\\), \\[(%s + %s)^2 \\le %d\\,(x^2 + y^2).\\]" % (tmono(p, "x"), tmono(q, "y"), S)
        stmt = "(x y : ℝ) :\n    (%s + %s) ^ 2 ≤ %d * (x ^ 2 + y ^ 2)" % (mono(p, "x"), mono(q, "y"), S)
        proof = "by\n  nlinarith [sq_nonneg (%s - %s)]" % (mono(q, "x"), mono(p, "y"))
        return informal, [Theorem("cauchy_two", stmt, proof, "A two-term Cauchy-Schwarz bound.")]
    if difficulty == 2:
        u, v, w = rng.choice(TRIPLES2)
        if rng.random() < 0.5: u, v = v, u
        sv = rng.choice([1, -1]); s = rng.randrange(1, 6); B = w * s
        for k in range(0, 360):
            x, y = F(s * math.cos(k * math.pi / 180)).limit_denominator(1000), F(s * math.sin(k * math.pi / 180)).limit_denominator(1000)
            if x * x + y * y <= s * s: assert u * x + sv * v * y <= B
        form = sgn_term(u, "x", True) + sgn_term(sv * v, "y")
        tform = sgn_term(u, "x", True, True) + sgn_term(sv * v, "y", False, True)
        informal = ("Let \\(x\\) and \\(y\\) be real numbers with \\(x^2 + y^2 \\le %d\\). Prove that \\(%s \\le %d\\)." % (s * s, tform, B))
        stmt = "(x y : ℝ) (h : x ^ 2 + y ^ 2 ≤ %d) :\n    %s ≤ %d" % (s * s, form, B)
        proof = ("by\n  have h1 : (%s) ^ 2 ≤ %d ^ 2 := by\n    nlinarith [sq_nonneg (%s - %s)]\n  by_contra hc\n  push_neg at hc\n  nlinarith [h1, hc]"
                 % (form, B, mono(v, "x"), ("(%d) * y" % (sv * u)) if sv * u != 1 else "y"))
        return informal, [Theorem("cauchy_bound_circle", stmt, proof, "A linear form is bounded on a disc by the Cauchy-Schwarz inequality.")]
    u, v, w, t = rng.choice(TRIPLES3)
    cs = [u, v, w]; rng.shuffle(cs)
    cs = [c * rng.choice([1, -1]) for c in cs]
    s = rng.randrange(1, 5); B = t * s
    assert sum(c * c for c in cs) == t * t
    # exact check on the boundary points in the direction of the coefficient vector and a few others
    for x, y, z in [(F(c * s, t) for c in cs), (F(s, 3), F(-s, 3), F(s, 3)), (F(0), F(s), F(0))]:
        if x * x + y * y + z * z <= s * s: assert cs[0] * x + cs[1] * y + cs[2] * z <= B
    form = sgn_term(cs[0], "x", True) + sgn_term(cs[1], "y") + sgn_term(cs[2], "z")
    tform = sgn_term(cs[0], "x", True, True) + sgn_term(cs[1], "y", False, True) + sgn_term(cs[2], "z", False, True)
    informal = ("Prove that for all real numbers \\(u, v, w, x, y, z\\), \\[(ux + vy + wz)^2 \\le (u^2 + v^2 + w^2)(x^2 + y^2 + z^2).\\] "
                "Then let \\(x, y, z\\) be real numbers with \\(x^2 + y^2 + z^2 \\le %d\\) and prove that \\(%s \\le %d\\)." % (s * s, tform, B))
    lemma = Theorem("cauchy_three", "(u v w x y z : ℝ) :\n    (u * x + v * y + w * z) ^ 2 ≤ (u ^ 2 + v ^ 2 + w ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)",
                    "by\n  nlinarith [sq_nonneg (u * y - v * x), sq_nonneg (u * z - w * x), sq_nonneg (v * z - w * y)]",
                    "Cauchy-Schwarz for three-term sums.")
    inst = " ".join("(%d)" % c if c < 0 else "%d" % c for c in cs)
    main = Theorem("cauchy_bound_ball", "(x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 ≤ %d) :\n    %s ≤ %d" % (s * s, form, B),
                   "by\n  have h1 := cauchy_three %s x y z\n  by_contra hc\n  push_neg at hc\n  nlinarith [h1, hc]" % inst,
                   "A linear form is bounded on a ball.", weight=2.0)
    return informal, [lemma, main]


# ---------------------------------------------------------------- abs_ineq
def abs_ineq(rng, difficulty):
    if difficulty == 1:
        p, q = rng.randrange(1, 10), rng.randrange(1, 10)
        a, b = rng.randrange(-9, 10), rng.randrange(-9, 10); r, s = rng.randrange(1, 10), rng.randrange(1, 10)
        K = p * a - q * b; bound = p * r + q * s
        for x in (a - r, a + r, a):
            for y in (b - s, b + s, b): assert abs(p * x - q * y - K) <= bound
        expr = sgn_term(p, "x", True) + sgn_term(-q, "y") + ((" + %d" % -K if -K > 0 else " - %d" % K) if K != 0 else "")
        tex = expr.replace(" * ", "")
        informal = ("Let \\(x\\) and \\(y\\) be real numbers with \\(|%s| \\le %d\\) and \\(|%s| \\le %d\\). Prove that \\(|%s| \\le %d\\)."
                    % (shift("x", -a), r, shift("y", -b), s, tex, bound))
        stmt = "(x y : ℝ) (hx : |%s| ≤ %d) (hy : |%s| ≤ %d) :\n    |%s| ≤ %d" % (shift("x", -a), r, shift("y", -b), s, expr, bound)
        proof = "by\n  rw [abs_le] at hx hy ⊢\n  obtain ⟨h1, h2⟩ := hx\n  obtain ⟨h3, h4⟩ := hy\n  constructor <;> linarith"
        return informal, [Theorem("abs_linear_bound", stmt, proof, "An error bound for a linear combination.")]
    if difficulty == 2 and rng.random() < 0.5:
        p = rng.randrange(1, 7); a = rng.randrange(1, 10); gap = rng.randrange(1, 13); b = a + gap
        for x in range(-20, 30): assert p * gap <= p * abs(x - a) + p * abs(x - b)
        K = p * gap
        informal = "Prove that for every real number \\(x\\), \\[%d \\le %s|x - %d| + %s|x - %d|.\\]" % (K, tmono(p, ""), a, tmono(p, ""), b)
        stmt = "(x : ℝ) :\n    %d ≤ %s + %s" % (K, mono(p, "|x - %d|" % a), mono(p, "|x - %d|" % b))
        proof = ("by\n  rcases abs_cases (x - %d) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (x - %d) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> linarith" % (a, b))
        return informal, [Theorem("abs_two_points", stmt, proof, "The sum of two distances is at least p times the gap.")]
    if difficulty == 2:
        a = rng.choice([c for c in range(-7, 8) if c != 0]); r = rng.randrange(1, 6); A = abs(a)
        bound = r * (r + 2 * A)
        for k in range(-20, 21):
            x = F(a) + F(k, 20) * r
            assert abs(x * x - a * a) <= bound
        informal = "Let \\(x\\) be a real number with \\(|%s| \\le %d\\). Prove that \\(|x^2 - %s^2| \\le %d\\)." % (shift("x", -a), r, ("(%d)" % a) if a < 0 else a, bound)
        ap = "(%d)" % a if a < 0 else "%d" % a
        stmt = "(x : ℝ) (h : |%s| ≤ %d) :\n    |x ^ 2 - %s ^ 2| ≤ %d * (%d + 2 * %d)" % (shift("x", -a), r, ap, r, r, A)
        informal = informal.replace("\\le %d\\)." % bound, "\\le %d(%d + %d)\\)." % (r, r, 2 * A))
        proof = ("by\n  have h1 : |%s| ≤ %d + 2 * %d := by\n    rw [abs_le] at h ⊢\n    constructor <;> linarith [h.1, h.2]\n"
                 "  have h2 : |x ^ 2 - %s ^ 2| = |%s| * |%s| := by\n    rw [← abs_mul]\n    congr 1\n    ring\n"
                 "  rw [h2]\n  exact mul_le_mul h h1 (abs_nonneg _) (by norm_num)" % (shift("x", a), r, A, ap, shift("x", -a), shift("x", a)))
        return informal, [Theorem("abs_square_bound", stmt, proof, "A bound on a difference of squares near a point.")]
    pts = sorted(rng.randrange(1, 10) for _ in range(4)); a, b, c, e = pts
    K = (e - a) + (c - b)
    for x in range(-5, 20): assert K <= abs(x - a) + abs(x - b) + abs(x - c) + abs(x - e)
    informal = ("Prove that for all real numbers \\(a \\le c\\) and \\(x\\), \\(c - a \\le |x - a| + |x - c|\\). "
                "Then prove that for every real \\(x\\), \\[%d \\le |x - %d| + |x - %d| + |x - %d| + |x - %d|.\\]" % (K, a, b, c, e))
    lemma = Theorem("pair_abs_bound", "(x a c : ℝ) (h : a ≤ c) :\n    c - a ≤ |x - a| + |x - c|",
                    "by\n  rcases abs_cases (x - a) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (x - c) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> linarith",
                    "The sum of the distances to two points is at least their gap.")
    main = Theorem("four_points_abs", "(x : ℝ) :\n    %d ≤ |x - %d| + |x - %d| + |x - %d| + |x - %d|" % (K, a, b, c, e),
                   "by\n  have h1 := pair_abs_bound x %d %d (by norm_num)\n  have h2 := pair_abs_bound x %d %d (by norm_num)\n  linarith" % (a, e, b, c),
                   "The sum of four distances is bounded below.", weight=2.0)
    return informal, [lemma, main]


# ---------------------------------------------------------------- monotone
# name: (lean template, tex template, python function, proof of T(x) <= T(y) from h [and hx])
UNCOND = {
    "exp": ("Real.exp %s", "e^{%s}", math.exp, "Real.exp_le_exp.2 h"),
    "cube": ("%s ^ 3", "%s^3", lambda t: t ** 3, "(Odd.strictMono_pow (by decide : Odd 3)).monotone h"),
    "quint": ("%s ^ 5", "%s^5", lambda t: t ** 5, "(Odd.strictMono_pow (by decide : Odd 5)).monotone h"),
    "arctan": ("Real.arctan %s", "\\arctan %s", math.atan, "Real.arctan_strictMono.monotone h"),
    "sinh": ("Real.sinh %s", "\\sinh %s", math.sinh, "Real.sinh_strictMono.monotone h"),
}
COND = {   # need 0 < x
    "sqrt": ("Real.sqrt %s", "\\sqrt{%s}", math.sqrt, "Real.sqrt_le_sqrt h"),
    "log": ("Real.log %s", "\\ln %s", math.log, "Real.log_le_log hx h"),
    "sq": ("%s ^ 2", "%s^2", lambda t: t * t, "pow_le_pow_left₀ hx.le h 2"),
}
LOG1SQ = ("Real.log (1 + %s ^ 2)", "\\ln(1 + %s^2)", lambda t: math.log(1 + t * t))


def mono_expr(terms, c0, var, tex=False):
    """terms: list of (coef, template) ; c0 coefficient of the linear term (0 for none)."""
    parts = []
    for c, t in terms:
        parts.append((c, t % var))
    if c0: parts.append((c0, var))
    out = ""
    for i, (c, body) in enumerate(parts):
        if tex: out += ("" if i == 0 else " + ") + (body if c == 1 else "%d\\,%s" % (c, body))
        else: out += ("" if i == 0 else " + ") + (body if c == 1 else "%d * %s" % (c, body))
    return out


def monotone(rng, difficulty):
    names = sorted(UNCOND)
    if difficulty == 1:
        n1 = rng.choice(names); c1 = rng.randrange(1, 10); c0 = rng.randrange(0, 10)
        tm = [(c1, UNCOND[n1][0])]; tt = [(c1, UNCOND[n1][1])]
        f = lambda t: c1 * UNCOND[n1][2](t) + c0 * t
        for x, y in [(-1.5, -1.0), (-0.3, 0.2), (0.5, 2.0), (1.0, 1.0)]: assert f(x) <= f(y) + 1e-12
        informal = "Prove that for all real numbers \\(x \\le y\\), \\[%s \\le %s.\\]" % (mono_expr(tt, c0, "x", True), mono_expr(tt, c0, "y", True))
        stmt = "(x y : ℝ) (h : x ≤ y) :\n    %s ≤ %s" % (mono_expr(tm, c0, "x"), mono_expr(tm, c0, "y"))
        have = "  have h1 : %s ≤ %s := %s" % (UNCOND[n1][0] % "x", UNCOND[n1][0] % "y", UNCOND[n1][3])
        return informal, [Theorem("monotone_sum", stmt, "by\n%s\n  linarith" % have, "The function is non-decreasing.")]
    if difficulty == 2:
        k = rng.choice([2, 3]); chosen = rng.sample(names, k)
        cs = [rng.randrange(1, 7) for _ in chosen]; c0 = rng.choice([0, 0, rng.randrange(1, 6)])
        tm = [(c, UNCOND[n][0]) for c, n in zip(cs, chosen)]; tt = [(c, UNCOND[n][1]) for c, n in zip(cs, chosen)]
        f = lambda t: sum(c * UNCOND[n][2](t) for c, n in zip(cs, chosen)) + c0 * t
        for x, y in [(-1.5, -1.0), (-0.3, 0.2), (0.5, 2.0), (-2.0, 2.0)]: assert f(x) <= f(y) + 1e-12
        informal = "Prove that the function \\(f(x) = %s\\) is monotone on the real numbers: \\(x \\le y\\) implies \\(f(x) \\le f(y)\\)." % mono_expr(tt, c0, "x", True)
        stmt = ": Monotone (fun x : ℝ => %s)" % mono_expr(tm, c0, "x")
        haves = "\n".join("  have h%d : %s ≤ %s := %s" % (i + 1, UNCOND[n][0] % "x", UNCOND[n][0] % "y", UNCOND[n][3]) for i, n in enumerate(chosen))
        proof = "by\n  intro x y h\n%s\n  show %s ≤ %s\n  linarith" % (haves, mono_expr(tm, c0, "x"), mono_expr(tm, c0, "y"))
        return informal, [Theorem("monotone_function", stmt, proof, "The function is monotone.")]
    cn = rng.sample(sorted(COND), rng.choice([1, 2])); un = rng.sample(names, rng.choice([1, 2]))
    c_log = rng.randrange(1, 6)
    items = [(rng.randrange(1, 6), "u", n) for n in un] + [(rng.randrange(1, 6), "c", n) for n in cn]
    rng.shuffle(items)
    items.append((c_log, "l", "log1sq"))
    tm = []; tt = []
    for c, kind, n in items:
        tpl = LOG1SQ if kind == "l" else (UNCOND if kind == "u" else COND)[n]
        tm.append((c, tpl[0])); tt.append((c, tpl[1]))
    def pyf(t):
        s = 0.0
        for c, kind, n in items:
            fn = LOG1SQ[2] if kind == "l" else (UNCOND if kind == "u" else COND)[n][2]
            s += c * fn(t)
        return s
    for x, y in [(0.1, 0.5), (0.5, 0.5), (0.3, 4.0), (1.0, 9.0)]: assert pyf(x) <= pyf(y) + 1e-12
    informal = ("Prove that \\(0 \\le \\ln(1 + y^2) - \\ln(1 + x^2)\\) for real numbers \\(0 < x \\le y\\). Then prove that for such \\(x, y\\), \\[0 \\le \\left(%s\\right) - \\left(%s\\right).\\]"
                % (mono_expr(tt, 0, "y", True), mono_expr(tt, 0, "x", True)))
    lemma = Theorem("log_one_add_sq_mono", "(x y : ℝ) (hx : 0 < x) (h : x ≤ y) :\n    0 ≤ Real.log (1 + y ^ 2) - Real.log (1 + x ^ 2)",
                    "by\n  have hy : 0 < y := lt_of_lt_of_le hx h\n  have h3 : Real.log (1 + x ^ 2) ≤ Real.log (1 + y ^ 2) := by\n    apply Real.log_le_log (by positivity)\n    nlinarith [mul_pos hx hy, mul_nonneg (sub_nonneg.2 h) hx.le]\n  linarith",
                    "The logarithm of one plus a square is increasing on the positive reals.")
    haves = []
    for i, (c, kind, n) in enumerate(items):
        if kind == "l":
            haves.append("  have h%d := log_one_add_sq_mono x y hx h" % (i + 1)); continue
        tpl, pr = (UNCOND if kind == "u" else COND)[n][0], (UNCOND if kind == "u" else COND)[n][3]
        haves.append("  have h%d : %s ≤ %s := %s" % (i + 1, tpl % "x", tpl % "y", pr))
    main = Theorem("monotone_combination", "(x y : ℝ) (hx : 0 < x) (h : x ≤ y) :\n    0 ≤ (%s) - (%s)" % (mono_expr(tm, 0, "y"), mono_expr(tm, 0, "x")),
                   "by\n%s\n  linarith" % "\n".join(haves), "The combination is non-decreasing on the positive reals.", weight=2.0)
    return informal, [lemma, main]


def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    informal, theorems = {"amgm": amgm, "cauchy": cauchy, "abs_ineq": abs_ineq, "monotone": monotone}[family](rng, difficulty)
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove",
                title="Prove an inequality over the reals", informal=informal, theorems=theorems)
