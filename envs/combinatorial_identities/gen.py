"""Combinatorial identities and counting (MSC 05: combinatorics; 05A10, 05A19, 05D05).

Families: sums of binomial coefficients; Fibonacci identities by induction; closed forms for
linear recurrences defined in a preamble; counting with injections and the pigeonhole principle.
Second code path: every identity is checked in Python on small cases (math.comb, a direct
Fibonacci/recurrence loop, brute-force pigeonhole and injection counts) before it is returned.
"""
from math import comb
from itertools import combinations
from arena.core import Task, Theorem, rng_for

ENV = "combinatorial_identities"
FAMILIES = ["binomial_sums", "counting", "fibonacci", "linear_recurrence"]

def fibs(n):
    f = [0, 1]
    while len(f) <= n: f.append(f[-1] + f[-2])
    return f

# ---------------------------------------------------------------- binomial sums
def binomial_sums(rng, difficulty):
    if difficulty == 1:
        a = rng.randrange(2, 10)
        assert all(sum(comb(n, i) * a ** i for i in range(n + 1)) == (a + 1) ** n for n in range(9))
        stmt = "(n : ℕ) :\n    ∑ i ∈ Finset.range (n + 1), n.choose i * %d ^ i = %d ^ n" % (a, a + 1)
        proof = ("by\n  have h := (add_pow (%d : ℕ) 1 n).symm\n  simp only [one_pow, mul_one, Nat.cast_id] at h\n  rw [Finset.sum_congr rfl (fun i _ => mul_comm (n.choose i) (%d ^ i))]\n  exact h" % (a, a))
        info = "For every natural number \\(n\\), \\[\\sum_{i=0}^{n} \\binom{n}{i}\\, %d^{i} = %d^{n}.\\]" % (a, a + 1)
        return info, [Theorem("binomial_sum", stmt, proof, "A weighted sum of binomial coefficients.")]
    if difficulty == 2:
        k = rng.randrange(1, 8); c = rng.choice([1, 1, 2, 3, 5])
        assert all(sum(c * comb(i + k, k) for i in range(n + 1)) == c * comb(n + k + 1, k + 1) for n in range(10))
        stmt = "(n : ℕ) :\n    ∑ i ∈ Finset.range (n + 1), %s(i + %d).choose %d = %s(n + %d).choose %d" % (
            ("%d * " % c) if c != 1 else "", k, k, ("%d * " % c) if c != 1 else "", k + 1, k + 1)
        proof = ("by\n  rw [← Finset.mul_sum, Nat.sum_range_add_choose n %d]" % k) if c != 1 else "by\n  exact Nat.sum_range_add_choose n %d" % k
        info = "For every natural number \\(n\\), \\[%s\\sum_{i=0}^{n} \\binom{i+%d}{%d} = %s\\binom{n+%d}{%d}.\\]" % (("%d \\cdot " % c) if c != 1 else "", k, k, ("%d \\cdot " % c) if c != 1 else "", k + 1, k + 1)
        info += " (This is the hockey stick identity.)"
        return info, [Theorem("hockey_stick", stmt, proof, "A hockey stick identity for binomial coefficients.")]
    a = rng.randrange(1, 6); c = rng.randrange(1, 8)
    def lhs(n): return sum((a * i + c) * comb(n, i) for i in range(n + 1))
    assert all(lhs(n) == a * n * 2 ** max(n - 1, 0) + c * 2 ** n for n in range(10))
    lemma = Theorem("sum_i_choose", "(n : ℕ) :\n    ∑ i ∈ Finset.range (n + 1), i * n.choose i = n * 2 ^ (n - 1)", "by\n  exact Nat.sum_range_mul_choose n", "The sum of i times n choose i.")
    main = Theorem("weighted_sum", "(n : ℕ) :\n    ∑ i ∈ Finset.range (n + 1), (%d * i + %d) * n.choose i = %d * (n * 2 ^ (n - 1)) + %d * 2 ^ n" % (a, c, a, c),
        "by\n  have h1 := sum_i_choose n\n  have h2 := Nat.sum_range_choose n\n  have e : ∀ i : ℕ, (%d * i + %d) * n.choose i = %d * (i * n.choose i) + %d * n.choose i := fun i => by ring\n  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]" % (a, c, a, c),
        "A weighted binomial sum.", weight=2.0)
    info = ("First prove \\[\\sum_{i=0}^{n} i \\binom{n}{i} = n \\cdot 2^{n-1},\\] where \\(n - 1\\) is truncated subtraction on the natural numbers. Then use it, and the value of \\(\\sum_{i=0}^{n} \\binom{n}{i}\\), to prove "
            "\\[\\sum_{i=0}^{n} (%di + %d) \\binom{n}{i} = %d \\cdot n \\cdot 2^{n-1} + %d \\cdot 2^{n}.\\]") % (a, c, a, c)
    return info, [lemma, main]

# ---------------------------------------------------------------- Fibonacci
def fibonacci(rng, difficulty):
    f = fibs(120)
    if difficulty == 1:
        a = rng.randrange(0, 15)
        assert all(sum(f[i + a] for i in range(n)) + f[a + 1] == f[n + a + 1] for n in range(12))
        stmt = "(n : ℕ) :\n    ∑ i ∈ Finset.range n, Nat.fib (i + %d) + Nat.fib %d = Nat.fib (n + %d)" % (a, a + 1, a + 1)
        proof = ("by\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    have e : Nat.fib (k + 1 + %d) = Nat.fib (k + %d) + Nat.fib (k + %d) := by\n      rw [show k + 1 + %d = (k + %d) + 2 from by omega, show k + %d = (k + %d) + 1 from by omega]\n      exact Nat.fib_add_two\n    rw [Finset.sum_range_succ, e]\n    omega" % (a + 1, a, a + 1, a + 1, a, a + 1, a))
        info = "For every natural number \\(n\\), with \\(F\\) the Fibonacci sequence (\\(F_0 = 0\\), \\(F_1 = 1\\), \\(F_{k+2} = F_k + F_{k+1}\\)), \\[\\sum_{i=0}^{n-1} F_{i+%d} + F_{%d} = F_{n+%d}.\\]" % (a, a + 1, a + 1)
        return info, [Theorem("fib_shifted_sum", stmt, proof, "A telescoping sum of Fibonacci numbers.")]
    if difficulty == 2:
        if rng.random() < 0.5:
            a = rng.randrange(0, 12)
            assert all(sum(f[2 * i + a + 1] for i in range(n)) + f[a] == f[2 * n + a] for n in range(12))
            stmt = "(n : ℕ) :\n    ∑ i ∈ Finset.range n, Nat.fib (2 * i + %d) + Nat.fib %d = Nat.fib (2 * n + %d)" % (a + 1, a, a)
            proof = ("by\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    have e : Nat.fib (2 * (k + 1) + %d) = Nat.fib (2 * k + %d) + Nat.fib (2 * k + %d) := by\n      rw [show 2 * (k + 1) + %d = (2 * k + %d) + 2 from by omega, show 2 * k + %d = (2 * k + %d) + 1 from by omega]\n      exact Nat.fib_add_two\n    rw [Finset.sum_range_succ, e]\n    omega" % (a, a, a + 1, a, a, a + 1, a))
            info = "For every natural number \\(n\\), with \\(F\\) the Fibonacci sequence, \\[\\sum_{i=0}^{n-1} F_{2i+%d} + F_{%d} = F_{2n+%d}.\\]" % (a + 1, a, a)
            return info, [Theorem("fib_odd_sum", stmt, proof, "A sum of every second Fibonacci number.")]
        c = rng.randrange(1, 9)
        assert all(sum(c * f[i] ** 2 for i in range(n + 1)) == c * f[n] * f[n + 1] for n in range(12))
        stmt = "(n : ℕ) :\n    ∑ i ∈ Finset.range (n + 1), %d * Nat.fib i ^ 2 = %d * (Nat.fib n * Nat.fib (n + 1))" % (c, c)
        proof = "by\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    rw [Finset.sum_range_succ, ih, Nat.fib_add_two (n := k)]\n    ring"
        info = "For every natural number \\(n\\), with \\(F\\) the Fibonacci sequence, \\[\\sum_{i=0}^{n} %d\\,F_i^2 = %d\\,F_n F_{n+1}.\\]" % (c, c)
        return info, [Theorem("fib_square_sum", stmt, proof, "A sum of squares of Fibonacci numbers.")]
    while True:
        c = rng.randrange(1, 8); b = rng.randrange(0, 9)
        if (c, b) != (1, 0): break
    for n in range(10):
        idx = c * n + b
        assert f[idx + 1] ** 2 - f[idx] * f[idx + 2] == (-1) ** idx
    lemma = Theorem("cassini", "(n : ℕ) :\n    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n",
        "by\n  induction n with\n  | zero => simp\n  | succ k ih =>\n    have e1 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two\n    have e2 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two\n    rw [e2, pow_succ]\n    rw [e1] at ih ⊢\n    push_cast at ih ⊢\n    linear_combination (-1 : ℤ) * ih",
        "Cassini's identity for Fibonacci numbers.")
    cn = ("%d * n" % c) if c != 1 else "n"
    idx = ("%s + %d" % (cn, b)) if b else cn
    main = Theorem("cassini_pm_one", "(n : ℕ) :\n    (Nat.fib (%s + 1) : ℤ) ^ 2 - Nat.fib (%s) * Nat.fib (%s + 2) = 1 ∨ (Nat.fib (%s + 1) : ℤ) ^ 2 - Nat.fib (%s) * Nat.fib (%s + 2) = -1" % ((idx,) * 6),
        "by\n  rw [cassini (%s)]\n  rcases neg_one_pow_eq_or ℤ (%s) with h | h\n  · exact Or.inl h\n  · exact Or.inr h" % (idx, idx),
        "Cassini's determinant is plus or minus one at the index given.", weight=2.0)
    info = ("First prove Cassini's identity: for every natural number \\(n\\), \\[F_{n+1}^2 - F_n F_{n+2} = (-1)^n,\\] computed in the integers, where \\(F\\) is the Fibonacci sequence. "
            "Then conclude that \\(F_{m+1}^2 - F_m F_{m+2}\\) is either \\(1\\) or \\(-1\\) when \\(m = %s\\).") % (("%sn + %d" % ("" if c == 1 else c, b)) if b else "%sn" % ("" if c == 1 else c))
    return info, [lemma, main]

# ---------------------------------------------------------------- linear recurrences
def linear_recurrence(rng, difficulty):
    def sgn(x): return "(%d)" % x if x < 0 else "%d" % x
    if difficulty < 3:
        pool = [1, 2, 3, 4, 5] if difficulty == 1 else [-4, -3, -2, -1, 1, 2, 3, 4, 5]
        r, s = rng.sample(pool, 2)
        A = rng.choice([x for x in range(-3, 5) if x]); B = rng.choice([x for x in range(-3, 5) if x])
        u0, u1 = A + B, A * r + B * s; p, q = r + s, r * s
        closed = lambda n: A * r ** n + B * s ** n
        form = "%s * %s ^ n + %s * %s ^ n" % (sgn(A), sgn(r), sgn(B), sgn(s))
        tx = "%d \\cdot %s^{n} + %d \\cdot %s^{n}" % (A, "(%d)" % r if r < 0 else r, B, "(%d)" % s if s < 0 else s)
        desc_roots = "\\(%s\\) and \\(%s\\)" % (r, s)
    else:
        r = rng.choice([-3, -2, -1, 2, 3, 4]); A = rng.choice([x for x in range(-3, 5) if x]); B = rng.choice([x for x in range(-3, 5) if x])
        u0, u1 = A, (A + B) * r; p, q = 2 * r, r * r
        closed = lambda n: (A + B * n) * r ** n
        form = "(%s + %s * (n : ℤ)) * %s ^ n" % (sgn(A), sgn(B), sgn(r))
        tx = "(%d + %d n) \\cdot %s^{n}" % (A, B, "(%d)" % r if r < 0 else r)
    seq = [u0, u1]
    while len(seq) < 15: seq.append(p * seq[-1] - q * seq[-2])
    assert all(seq[n] == closed(n) for n in range(15))
    rec = "%s * u (n + 1) - %s * u n" % (sgn(p), sgn(q))
    pre = "def u : ℕ → ℤ\n  | 0 => %s\n  | 1 => %s\n  | (n + 2) => %s" % (sgn(u0), sgn(u1), rec)
    stmt = "(n : ℕ) :\n    u n = %s" % form
    proof = ("by\n  induction n using Nat.strong_induction_on with\n  | _ n ih =>\n    match n, ih with\n    | 0, _ => norm_num [u]\n    | 1, _ => norm_num [u]\n"
             "    | n + 2, ih =>\n      have h1 := ih (n + 1) (by omega)\n      have h0 := ih n (by omega)\n      rw [u, h1, h0]\n      push_cast\n      ring")
    info = ("Define a sequence of integers by \\(u_0 = %d\\), \\(u_1 = %d\\) and \\(u_{n+2} = %d\\,u_{n+1} - %d\\,u_{n}\\). Prove that for every natural number \\(n\\), \\[u_n = %s.\\]" % (u0, u1, p, q, tx))
    return info, pre, [Theorem("seq_closed_form", stmt, proof, "A closed form for the sequence defined by the recurrence.")]

# ---------------------------------------------------------------- counting
def counting(rng, difficulty):
    if difficulty == 1:
        m = rng.randrange(2, 9)
        # brute-force check: any m+1 integers in a window contain two with the same residue
        for _ in range(50):
            xs = rng.sample(range(-20, 20), m + 1)
            assert len({x % m for x in xs}) <= m
        stmt = "(s : Finset ℤ) (h : %d < s.card) :\n    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x %% %d = y %% %d" % (m, m, m)
        proof = ("by\n  have hmaps : Set.MapsTo (fun x : ℤ => x %% %d) (s : Set ℤ) (Finset.Ico (0 : ℤ) %d : Finset ℤ) := by\n    intro x _\n    simp only [Finset.coe_Ico, Set.mem_Ico]\n    omega\n"
                 "  have hc : (Finset.Ico (0 : ℤ) %d).card < s.card := by simpa using h\n  exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps" % (m, m, m))
        info = "Let \\(s\\) be a finite set of integers with more than %d elements. Prove that \\(s\\) contains two different integers \\(x \\ne y\\) that leave the same remainder on division by %d." % (m, m)
        return info, [], [Theorem("pigeonhole_mod", stmt, proof, "Pigeonhole principle for remainders.")]
    if difficulty == 2:
        p = rng.randrange(2, 7); r = rng.randrange(0, p)
        for n in range(1, 15):
            assert len([y for y in range(p * n) if y % p == r]) == n >= n
        stmt = "(n : ℕ) :\n    (Finset.range n).card ≤ ((Finset.range (%d * n)).filter (fun y => y %% %d = %d)).card" % (p, p, r)
        proof = ("by\n  apply Finset.card_le_card_of_injOn (fun x => %d * x + %d)\n  · intro x hx\n    simp only [Finset.coe_range, Set.mem_Iio] at hx\n    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]\n    constructor <;> omega\n"
                 "  · intro x _ y _ h\n    simp only at h\n    omega" % (p, r))
        info = "Let \\(n\\) be a natural number. Prove that the set \\(\\{0, 1, \\dots, n-1\\}\\) has at most as many elements as the set of integers \\(y\\) with \\(0 \\le y < %d n\\) and \\(y \\equiv %d \\pmod{%d}\\). (Construct an injection.)" % (p, r, p)
        return info, [], [Theorem("card_le_residue_class", stmt, proof, "An injection into a residue class gives a cardinality bound.")]
    k = rng.randrange(2, 8); m = rng.randrange(2, 8)
    stmt = "(s : Finset ℕ) (hs : s ⊆ Finset.range (%d * %d)) (h : %d < s.card) :\n    ∃ x ∈ s, ∃ y ∈ s, x < y ∧ y < x + %d" % (k, m, m, k)
    proof = ("by\n  have hmaps : Set.MapsTo (fun x : ℕ => x / %d) (s : Set ℕ) (Finset.range %d : Finset ℕ) := by\n    intro x hx\n    have hx' := hs hx\n    simp only [Finset.mem_range] at hx'\n    simp only [Finset.coe_range, Set.mem_Iio]\n    omega\n"
             "  have hc : (Finset.range %d).card < s.card := by simpa using h\n  obtain ⟨x, hx, y, hy, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps\n"
             "  replace heq : x / %d = y / %d := heq\n  rcases lt_or_gt_of_ne hne with hlt | hgt\n  · exact ⟨x, hx, y, hy, hlt, by omega⟩\n  · exact ⟨y, hy, x, hx, hgt, by omega⟩" % (k, m, m, k, k))
    info = ("Let \\(s\\) be a set of natural numbers that are all less than \\(%d \\cdot %d = %d\\), and suppose \\(s\\) has more than %d elements. Prove that \\(s\\) contains two elements \\(x < y\\) with \\(y - x < %d\\)." % (k, m, k * m, m, k))
    return info, [], [Theorem("close_pair", stmt, proof, "Pigeonhole principle for blocks of consecutive numbers.")]

def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    pre = ""
    if family == "linear_recurrence":
        info, pre, thms = linear_recurrence(rng, difficulty)
    elif family == "counting":
        info, _, thms = counting(rng, difficulty)
    else:
        info, thms = {"binomial_sums": binomial_sums, "fibonacci": fibonacci}[family](rng, difficulty)
    titles = {"binomial_sums": "Prove an identity for binomial coefficients", "fibonacci": "Prove an identity for Fibonacci numbers",
              "linear_recurrence": "Find the closed form of a recurrence", "counting": "Prove a counting statement"}
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove", title=titles[family],
        informal="Prove the following.\n\n" + info, preamble=pre, theorems=thms)
