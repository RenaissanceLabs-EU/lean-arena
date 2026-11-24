"""Real analysis from the definitions (MSC 26: real functions; 26A03, 26A15, 26D05).

Families: limits of explicit sequences stated by the epsilon-N definition; epsilon-delta continuity
of explicit functions; bounds and monotonicity of recursively defined real sequences; uniform
bounds and uniform convergence on intervals.
Second code path: the constants used in a statement (the limit, the bound, the fixed point) are
computed with exact fractions and checked against the recursion or the function on many points
before the task is returned.
"""
from fractions import Fraction as F
from arena.core import Task, Theorem, rng_for

ENV = "real_analysis"
FAMILIES = ["continuity", "limit_sequence", "sequence_bounds", "uniform_bounds"]

def lit(x):
    """Lean text of a rational constant as a real number."""
    x = F(x)
    if x.denominator == 1: return "(%d : ℝ)" % x.numerator
    return "(%d / %d : ℝ)" % (x.numerator, x.denominator)

def tex(x):
    x = F(x)
    if x.denominator == 1: return "%d" % x.numerator
    return ("-" if x < 0 else "") + "\\frac{%d}{%d}" % (abs(x.numerator), x.denominator)

def texp(x):
    """TeX of a constant used as a base or factor, parenthesized when needed."""
    x = F(x)
    return "(%s)" % tex(x) if x < 0 else tex(x)

def ptex(*terms):
    """TeX of a sum of integer-coefficient terms [(coef, 'x^2'), (coef, '')]: -x - 3, 7x + 1, ..."""
    out = ""
    for c, v in terms:
        if c == 0: continue
        body = v if (abs(c) == 1 and v) else "%d%s" % (abs(c), v)
        if not out: out = ("-" if c < 0 else "") + body
        else: out += (" - " if c < 0 else " + ") + body
    return out or "0"

def T(text, **kw):
    """Fill @name@ tokens: Lean literals for constants."""
    for k, v in kw.items(): text = text.replace("@%s@" % k, lit(v) if not isinstance(v, str) else v)
    assert "@" not in text, text
    return text

# ---------------------------------------------------------------- limits of sequences
def limit_sequence(rng, difficulty):
    n = "(n : ℝ)"
    if difficulty == 1:
        c = rng.randrange(1, 10); a = rng.randrange(1, 10)
        for m in range(1, 200):
            assert abs(F(c, m + a)) <= F(c, m)
        expr = "%s / (%s + %s)" % (lit(c), n, lit(a))
        stmt = ":\n    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |%s - 0| < ε" % expr
        proof = T("""by
  intro ε hε
  refine ⟨⌈@c@ / ε⌉₊, fun n hn => ?_⟩
  have h1 : @c@ / ε ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : @c@ ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp h1
  have hpos : (0 : ℝ) < (n : ℝ) + @a@ := by positivity
  rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ hpos]
  nlinarith [mul_pos hε (by norm_num : (0 : ℝ) < @a@)]""", c=c, a=a)
        info = "Prove, directly from the definition of a limit, that the sequence \\(u_n = \\dfrac{%d}{n + %d}\\) tends to \\(0\\): for every \\(\\varepsilon > 0\\) there is \\(N\\) such that \\(|u_n - 0| < \\varepsilon\\) for all \\(n \\ge N\\)." % (c, a)
        return info, [], [Theorem("seq_limit", stmt, proof, "The sequence tends to 0 (epsilon-N definition).")]
    if difficulty == 2:
        while True:
            a = rng.choice([x for x in range(-5, 10) if x]); b = rng.randrange(-5, 10); c = rng.randrange(1, 7); d = rng.randrange(1, 10)
            if c * b - a * d != 0: break
        K = abs(c * b - a * d)
        for m in range(1, 100):
            assert F(a * m + b, c * m + d) - F(a, c) == F(c * b - a * d, c * (c * m + d))
        expr = "(%s * %s + %s) / (%s * %s + %s)" % (lit(a), n, lit(b), lit(c), n, lit(d))
        stmt = ":\n    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |%s - %s / %s| < ε" % (expr, lit(a), lit(c))
        proof = T("""by
  intro ε hε
  refine ⟨⌈@K@ / ε⌉₊, fun n hn => ?_⟩
  have h1 : @K@ / ε ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : @K@ ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp h1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (0 : ℝ) < @c@ * (n : ℝ) + @d@ := by positivity
  have e : @E@ - @a@ / @c@ = (@c@ * @b@ - @a@ * @d@) / (@c@ * (@c@ * (n : ℝ) + @d@)) := by
    field_simp
    ring
  have hk : |(@c@ * @b@ - @a@ * @d@ : ℝ)| = @K@ := by norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [e, abs_div, hk, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]
  nlinarith [mul_nonneg hn0 hε.le, hε]""", K=K, c=c, d=d, a=a, b=b, E=expr)
        info = "Prove, directly from the definition of a limit, that \\(u_n = \\dfrac{%s}{%s}\\) tends to \\(\\dfrac{%d}{%d}\\): for every \\(\\varepsilon > 0\\) there is \\(N\\) such that \\(\\left|u_n - \\frac{%d}{%d}\\right| < \\varepsilon\\) for all \\(n \\ge N\\)." % (ptex((a, "n"), (b, "")), ptex((c, "n"), (d, "")), a, c, a, c)
        return info, [], [Theorem("seq_limit", stmt, proof, "The sequence converges to a/c (epsilon-N definition).")]
    a = rng.randrange(1, 8); b = rng.randrange(0, 8); c = rng.randrange(1, 9)
    for m in range(1, 200):
        assert F(a * m + b, m * m + c) <= F(a + b, m)
    expr = "(%s * %s + %s) / (%s ^ 2 + %s)" % (lit(a), n, lit(b), n, lit(c))
    stmt = ":\n    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |%s - 0| < ε" % expr
    M = a + b
    proof = T("""by
  intro ε hε
  refine ⟨⌈@M@ / ε⌉₊ + 1, fun n hn => ?_⟩
  have h1 : @M@ / ε ≤ ((⌈@M@ / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h1' : (((⌈@M@ / ε⌉₊ + 1 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  push_cast at h1'
  have h2 : @M@ ≤ ((⌈@M@ / ε⌉₊ : ℕ) : ℝ) * ε := (div_le_iff₀ hε).mp h1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) ⌈@M@ / ε⌉₊]
  have hM : @M@ < (n : ℝ) * ε := by nlinarith
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 + @c@ := by positivity
  rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ hpos]
  nlinarith [mul_pos hε (by norm_num : (0 : ℝ) < @c@), mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ @b@), mul_pos hε (by linarith : (0 : ℝ) < (n : ℝ))]""", M=M, c=c, b=b)
    info = "Prove, directly from the definition of a limit, that \\(u_n = \\dfrac{%s}{n^2 + %d}\\) tends to \\(0\\): for every \\(\\varepsilon > 0\\) there is \\(N\\) such that \\(|u_n - 0| < \\varepsilon\\) for all \\(n \\ge N\\)." % (ptex((a, "n"), (b, "")), c)
    return info, [], [Theorem("seq_limit", stmt, proof, "The sequence tends to 0 (epsilon-N definition).")]

# ---------------------------------------------------------------- continuity
def continuity(rng, difficulty):
    x0 = rng.randrange(-4, 5)
    if difficulty == 1:
        a = rng.choice([x for x in range(-7, 8) if x]); b = rng.randrange(-6, 7); A = abs(a)
        for t in range(-20, 21):
            assert abs((a * t + b) - (a * x0 + b)) == A * abs(t - x0)
        stmt = ":\n    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - %s| < δ → |(%s * x + %s) - (%s * %s + %s)| < ε" % (lit(x0), lit(a), lit(b), lit(a), lit(x0), lit(b))
        proof = T("""by
  intro ε hε
  refine ⟨ε / @A@, by positivity, fun x hx => ?_⟩
  have e : (@a@ * x + @b@) - (@a@ * @x0@ + @b@) = @a@ * (x - @x0@) := by ring
  rw [e, abs_mul, show |@a@| = @A@ by norm_num]
  rw [lt_div_iff₀ (by norm_num)] at hx
  linarith""", A=A, a=a, b=b, x0=x0)
        info = "Prove, from the epsilon-delta definition, that \\(f(x) = %s\\) is continuous at \\(x_0 = %d\\): for every \\(\\varepsilon > 0\\) there is \\(\\delta > 0\\) such that \\(|f(x) - f(x_0)| < \\varepsilon\\) whenever \\(|x - x_0| < \\delta\\)." % (ptex((a, "x"), (b, "")), x0)
        return info, [Theorem("continuous_at", stmt, proof, "Epsilon-delta continuity of a linear function at a point.")]
    if difficulty == 2:
        a = rng.choice([x for x in range(-6, 7) if x]); b = rng.randrange(-6, 7); A = abs(a); X0 = abs(x0); P = A * (2 * X0 + 1)
        for t in [F(k, 7) for k in range(-60, 60)]:
            if abs(t - x0) < 1: assert abs(a * t * t - a * x0 * x0) <= P * abs(t - x0)
        stmt = ":\n    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - %s| < δ → |(%s * x ^ 2 + %s) - (%s * %s ^ 2 + %s)| < ε" % (lit(x0), lit(a), lit(b), lit(a), lit(x0), lit(b))
        proof = T("""by
  intro ε hε
  refine ⟨min 1 (ε / @P@), lt_min one_pos (by positivity), fun x hx => ?_⟩
  have h1 : |x - @x0@| < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - @x0@| < ε / @P@ := lt_of_lt_of_le hx (min_le_right _ _)
  have h3 : |x + @x0@| < 2 * @X0@ + 1 := by
    rw [abs_lt] at h1 ⊢
    constructor <;> norm_num <;> linarith [h1.1, h1.2]
  have e : (@a@ * x ^ 2 + @b@) - (@a@ * @x0@ ^ 2 + @b@) = @a@ * ((x - @x0@) * (x + @x0@)) := by ring
  rw [e, abs_mul, abs_mul, show |@a@| = @A@ by norm_num]
  have h4 : |x - @x0@| * @P@ < ε := by rwa [lt_div_iff₀ (by norm_num)] at h2
  have h5 := mul_le_mul_of_nonneg_left h3.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ @A@) (abs_nonneg (x - @x0@)))
  nlinarith [abs_nonneg (x - @x0@), abs_nonneg (x + @x0@)]""", P=P, x0=x0, X0=X0, a=a, b=b, A=A)
        info = "Prove, from the epsilon-delta definition, that \\(f(x) = %s\\) is continuous at \\(x_0 = %d\\): for every \\(\\varepsilon > 0\\) there is \\(\\delta > 0\\) such that \\(|f(x) - f(x_0)| < \\varepsilon\\) whenever \\(|x - x_0| < \\delta\\). Do not use any continuity lemma from the library." % (ptex((a, "x^2"), (b, "")), x0)
        return info, [Theorem("continuous_at", stmt, proof, "Epsilon-delta continuity of a quadratic function at a point.")]
    x0 = rng.randrange(1, 6); c = rng.randrange(1, 7)
    for t in [F(k, 9) for k in range(1, 100)]:
        if abs(t - x0) < F(x0, 2): assert abs(F(c) / t - F(c, x0)) * 1 <= F(2 * c, x0 * x0) * abs(t - x0)
    stmt = ":\n    ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - %s| < δ → |%s / x - %s / %s| < ε" % (lit(x0), lit(c), lit(c), lit(x0))
    proof = T("""by
  intro ε hε
  refine ⟨min (@x0@ / 2) (ε * @x0@ ^ 2 / (2 * @c@)), lt_min (by norm_num) (by positivity), fun x hx => ?_⟩
  have h1 : |x - @x0@| < @x0@ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - @x0@| < ε * @x0@ ^ 2 / (2 * @c@) := lt_of_lt_of_le hx (min_le_right _ _)
  have hx0 : @x0@ / 2 < x := by
    have := (abs_lt.mp h1).1
    linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have e : @c@ / x - @c@ / @x0@ = @c@ * (@x0@ - x) / (x * @x0@) := by
    field_simp
  have h3 : @c@ * |x - @x0@| < ε * @x0@ ^ 2 / 2 := by
    rw [lt_div_iff₀ (by norm_num)] at h2 ⊢
    nlinarith [abs_nonneg (x - @x0@)]
  have h4 : ε * @x0@ ^ 2 / 2 < ε * (x * @x0@) := by nlinarith [mul_pos hε (sub_pos.mpr hx0), mul_pos hε hxpos]
  rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < x * @x0@), abs_sub_comm, show |@c@| = @c@ by norm_num, div_lt_iff₀ (by positivity)]
  linarith""", x0=x0, c=c)
    info = "Prove, from the epsilon-delta definition, that \\(f(x) = \\dfrac{%d}{x}\\) is continuous at \\(x_0 = %d\\): for every \\(\\varepsilon > 0\\) there is \\(\\delta > 0\\) such that \\(|f(x) - f(x_0)| < \\varepsilon\\) whenever \\(|x - x_0| < \\delta\\). Here \\(x\\) ranges over all real numbers (in Lean, division by 0 gives 0, which does not matter for small \\(\\delta\\))." % (c, x0)
    return info, [Theorem("continuous_at", stmt, proof, "Epsilon-delta continuity of the reciprocal function at a point.")]

# ---------------------------------------------------------------- recursive sequences
def sequence_bounds(rng, difficulty):
    if difficulty < 3:
        c = F(rng.randrange(1, 9), rng.choice([1, 2, 3]))
        a0 = rng.choice([F(0), c / 2, c, 3 * c / 2, 2 * c])
        B = 2 * c
        a = [a0]
        for _ in range(40): a.append(a[-1] / 2 + c)
        assert all(0 <= x <= B for x in a) and all(a[i] <= a[i + 1] for i in range(40))
        pre = "noncomputable def a : ℕ → ℝ\n  | 0 => %s\n  | (n + 1) => a n / 2 + %s" % (lit(a0), lit(c))
        bound = Theorem("a_bounds", ":\n    ∀ n : ℕ, 0 ≤ a n ∧ a n ≤ %s" % lit(B),
            "by\n  intro n\n  induction n with\n  | zero => norm_num [a]\n  | succ k ih =>\n    obtain ⟨h0, h1⟩ := ih\n    simp only [a]\n    constructor <;> linarith")
        mono = Theorem("a_monotone", ":\n    Monotone a",
            "by\n  apply monotone_nat_of_le_succ\n  intro n\n  have h := (a_bounds n).2\n  simp only [a]\n  linarith", "The sequence is increasing.", weight=2.0)
        bound.informal = "The sequence stays between 0 and its upper bound."
        rec_tex = "a_{n+1} = \\frac{a_n}{2} + %s" % tex(c)
        info = "Define a real sequence by \\(a_0 = %s\\) and \\(%s\\)." % (tex(a0), rec_tex)
        if difficulty == 1:
            info += " Prove that \\(0 \\le a_n \\le %s\\) for every \\(n\\)." % tex(B)
            return info, pre, [bound]
        info += " Prove that \\(0 \\le a_n \\le %s\\) for every \\(n\\), and then that the sequence is monotone (non-decreasing)." % tex(B)
        return info, pre, [bound, mono]
    while True:
        u, v = rng.choice([(1, 2), (1, 3), (2, 3), (1, 4), (3, 4), (1, 5), (2, 5), (3, 5), (4, 5)])
        s = F(u, v); r = 1 - s
        a0 = rng.choice([F(0), r / 2, r / 3, r * 3 / 4, r])
        break
    c = 1 - s * s
    a = [a0]
    for _ in range(9): a.append((a[-1] ** 2 + c) / 2)
    assert all(0 <= x <= r for x in a) and all(a[i] <= a[i + 1] for i in range(9)) and r * r + c == 2 * r
    pre = "noncomputable def a : ℕ → ℝ\n  | 0 => %s\n  | (n + 1) => (a n ^ 2 + %s) / 2" % (lit(a0), lit(c))
    bound = Theorem("a_bounds", ":\n    ∀ n : ℕ, 0 ≤ a n ∧ a n ≤ %s" % lit(r),
        "by\n  intro n\n  induction n with\n  | zero => norm_num [a]\n  | succ k ih =>\n    obtain ⟨h0, h1⟩ := ih\n    have h2 : a k ^ 2 ≤ %s ^ 2 := by nlinarith\n    simp only [a]\n    constructor\n    · nlinarith [sq_nonneg (a k)]\n    · norm_num at h2 ⊢\n      linarith" % lit(r),
        "The sequence stays between 0 and the smaller fixed point.")
    mono = Theorem("a_monotone", ":\n    Monotone a",
        "by\n  apply monotone_nat_of_le_succ\n  intro n\n  obtain ⟨h0, h1⟩ := a_bounds n\n  simp only [a]\n  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ %s - a n)]" % lit(1 + s),
        "The sequence is increasing.", weight=2.0)
    info = ("Define a real sequence by \\(a_0 = %s\\) and \\(a_{n+1} = \\dfrac{a_n^2 + %s}{2}\\). Prove that \\(0 \\le a_n \\le %s\\) for every \\(n\\) (note that \\(%s\\) is a fixed point of the recursion), and then that the sequence is monotone (non-decreasing)."
            % (tex(a0), tex(c), tex(r), tex(r)))
    return info, pre, [bound, mono]

# ---------------------------------------------------------------- uniform bounds
def uniform_bounds(rng, difficulty):
    q = rng.choice([F(1, 2), F(1, 3), F(2, 3), F(3, 4), F(1, 4), F(3, 5), F(2, 5), F(4, 5)])
    c = rng.randrange(1, 10)
    if difficulty == 1:
        for n in range(8):
            for k in range(-20, 21):
                x = q * F(k, 20)
                assert abs(c * x ** (n + 1)) <= c * q ** (n + 1)
        stmt = ":\n    ∀ n : ℕ, ∀ x ∈ Set.Icc (-%s) %s, |%d * x ^ (n + 1)| ≤ %d * %s ^ (n + 1)" % (lit(q), lit(q), c, c, lit(q))
        proof = T("""by
  intro n x hx
  rw [abs_mul, abs_pow, show |(@c@)| = @c@ by norm_num]
  have hx' : |x| ≤ @q@ := abs_le.mpr ⟨hx.1, hx.2⟩
  have := pow_le_pow_left₀ (abs_nonneg x) hx' (n + 1)
  linarith""", c=c, q=q)
        info = "Prove that for every natural number \\(n\\) and every real \\(x\\) with \\(-%s \\le x \\le %s\\), \\[|%d\\,x^{n+1}| \\le %d \\cdot %s^{n+1}.\\]" % (tex(q), tex(q), c, c, texp(q))
        return info, [Theorem("uniform_bound", stmt, proof, "A bound that does not depend on the point x.")]
    if difficulty == 2:
        bound = F(1) / (1 - q)
        for n in range(12):
            for k in range(0, 21):
                x = q * F(k, 20)
                assert sum(x ** i for i in range(n)) <= bound
        stmt = ":\n    ∀ n : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) %s, ∑ i ∈ Finset.range n, x ^ i ≤ 1 / (1 - %s)" % (lit(q), lit(q))
        proof = T("""by
  intro n x hx
  have hq : (@q@ : ℝ) ≠ 1 := by norm_num
  have h1 : ∑ i ∈ Finset.range n, x ^ i ≤ ∑ i ∈ Finset.range n, (@q@ : ℝ) ^ i :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ hx.1 hx.2 i
  have h2 : ∑ i ∈ Finset.range n, (@q@ : ℝ) ^ i = (1 - @q@ ^ n) / (1 - @q@) := by
    rw [geom_sum_eq hq n, ← neg_sub, ← neg_sub 1, neg_div_neg_eq]
  have h3 : (1 - @q@ ^ n) / (1 - @q@) ≤ 1 / (1 - @q@) := by
    have : (0 : ℝ) < @q@ ^ n := by positivity
    apply div_le_div_of_nonneg_right (by linarith) (by norm_num)
  linarith""", q=q)
        info = "Prove that for every natural number \\(n\\) and every real \\(x\\) with \\(0 \\le x \\le %s\\), \\[\\sum_{i=0}^{n-1} x^{i} \\le \\frac{1}{1 - %s}.\\] The sum is empty when \\(n = 0\\)." % (tex(q), texp(q))
        return info, [Theorem("uniform_bound", stmt, proof, "A bound on partial geometric sums that does not depend on n or x.")]
    for n in range(1, 30):
        assert all(abs(c * (q * F(k, 20)) ** n) <= c * q ** n for k in range(-20, 21))
    stmt = ":\n    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |x| ≤ %s → |%d * x ^ n| < ε" % (lit(q), c)
    proof = T("""by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε (by norm_num : (0 : ℝ) < @c@)) (by norm_num : (@q@ : ℝ) < 1)
  refine ⟨N, fun n hn x hx => ?_⟩
  rw [abs_mul, abs_pow, show |(@c@)| = @c@ by norm_num]
  have h1 : |x| ^ n ≤ (@q@ : ℝ) ^ n := pow_le_pow_left₀ (abs_nonneg x) hx n
  have h2 : (@q@ : ℝ) ^ n ≤ (@q@ : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h3 : (@q@ : ℝ) ^ N < ε / @c@ := hN
  rw [lt_div_iff₀ (by norm_num)] at h3
  nlinarith""", c=c, q=q)
    info = "Prove that \\(c\\,x^n\\) with \\(c = %d\\) tends to \\(0\\) uniformly on \\([-%s, %s]\\): for every \\(\\varepsilon > 0\\) there is \\(N\\) such that \\(|%d\\,x^n| < \\varepsilon\\) for all \\(n \\ge N\\) and all real \\(x\\) with \\(|x| \\le %s\\)." % (c, tex(q), tex(q), c, tex(q))
    return info, [Theorem("uniform_convergence", stmt, proof, "Uniform convergence of a geometric sequence on an interval.")]

def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    pre = ""
    if family == "limit_sequence":
        info, _, thms = limit_sequence(rng, difficulty)
    elif family == "sequence_bounds":
        info, pre, thms = sequence_bounds(rng, difficulty)
    else:
        info, thms = {"continuity": continuity, "uniform_bounds": uniform_bounds}[family](rng, difficulty)
    titles = {"continuity": "Prove continuity from the epsilon-delta definition", "limit_sequence": "Prove a limit from the definition",
              "sequence_bounds": "Bound a recursive sequence", "uniform_bounds": "Prove a uniform bound"}
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove", title=titles[family],
        informal=info, preamble=pre, theorems=thms)
