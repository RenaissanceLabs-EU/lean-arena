"""Group theory (MSC 20: group theory and generalizations).

Families: involution (an exponent or inverse law forces commutativity), inverse (uniqueness and
cancellation facts in monoids and groups), subgroup (membership, normal subgroups, a union of two
subgroups, Lagrange with Nat.card), hom (kernels of group homomorphisms).
Second code path: numeric parameters (cyclic rotation, cardinalities) are checked in Python with
permutations and integer arithmetic before the task is returned; the Lean reference proofs are
compiled in the self-test.
"""
import itertools
from arena.core import Task, Theorem, rng_for

ENV = "group_theory"
FAMILIES = ["hom", "inverse", "involution", "subgroup"]
TYPES = ["G", "A", "Q"]
NAMES3 = [("x", "y", "z"), ("a", "b", "c"), ("g", "k", "m"), ("p", "q", "r"), ("u", "v", "w")]
NAMES2 = [("x", "y"), ("a", "b"), ("g", "k"), ("u", "v"), ("s", "t"), ("p", "q")]

def indent(text, n):
    pad = " " * n
    return "\n".join(pad + l if l.strip() else l for l in text.split("\n"))

def sub(n): return "".join("₀₁₂₃₄₅₆₇₈₉"[int(c)] for c in str(n))

# ---------------------------------------------------------------- involution

def inv_hyps(T, u, v):
    """kind -> (lean hypothesis, TeX hypothesis, proof of `∀ u v : T, u * v = v * u` from h)."""
    return {
        "self": ("∀ g : %s, g * g = 1" % T, "g \\cdot g = e \\text{ for every } g",
            "by\n  intro %s %s\n  have hi : ∀ g : %s, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)\n"
            "  calc %s * %s = (%s * %s)⁻¹ := (hi _).symm\n    _ = %s⁻¹ * %s⁻¹ := mul_inv_rev %s %s\n    _ = %s * %s := by rw [hi, hi]" % (u, v, T, u, v, u, v, v, u, u, v, v, u)),
        "inveq": ("∀ g : %s, g⁻¹ = g" % T, "g^{-1} = g \\text{ for every } g",
            "by\n  intro %s %s\n  calc %s * %s = (%s * %s)⁻¹ := (h _).symm\n    _ = %s⁻¹ * %s⁻¹ := mul_inv_rev %s %s\n    _ = %s * %s := by rw [h, h]" % (u, v, u, v, u, v, v, u, u, v, v, u)),
        "sq": ("∀ g : %s, g ^ 2 = 1" % T, "g^2 = e \\text{ for every } g",
            "by\n  intro %s %s\n  have hi : ∀ g : %s, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h g)\n"
            "  calc %s * %s = (%s * %s)⁻¹ := (hi _).symm\n    _ = %s⁻¹ * %s⁻¹ := mul_inv_rev %s %s\n    _ = %s * %s := by rw [hi, hi]" % (u, v, T, u, v, u, v, v, u, u, v, v, u)),
        "sqmul": ("∀ %s %s : %s, (%s * %s) ^ 2 = %s ^ 2 * %s ^ 2" % (u, v, T, u, v, u, v), "(ab)^2 = a^2 b^2 \\text{ for all } a, b",
            "by\n  intro %s %s\n  have h1 := h %s %s\n  simp only [pow_two, mul_assoc] at h1\n  have h2 := mul_left_cancel h1\n"
            "  have h3 : (%s * %s) * %s = (%s * %s) * %s := by simpa [mul_assoc] using h2\n  exact (mul_right_cancel h3).symm" % (u, v, u, v, v, u, v, u, v, v)),
        "invmul": ("∀ %s %s : %s, (%s * %s)⁻¹ = %s⁻¹ * %s⁻¹" % (u, v, T, u, v, u, v), "(ab)^{-1} = a^{-1} b^{-1} \\text{ for all } a, b",
            "by\n  intro %s %s\n  have h1 := h %s⁻¹ %s⁻¹\n  simp at h1\n  exact h1.symm" % (u, v, u, v)),
        "aba": ("∀ %(u)s %(v)s : %(T)s, %(u)s * %(v)s * %(u)s = %(v)s" % dict(u=u, v=v, T=T), "aba = b \\text{ for all } a, b",
            ("by\n  intro %(u)s %(v)s\n  have h1 : ∀ g : %(T)s, g * g = 1 := fun g => by\n    have := h g 1\n    rwa [mul_one] at this\n"
             "  calc %(u)s * %(v)s = %(u)s * %(v)s * (%(u)s * %(u)s) := by rw [h1 %(u)s, mul_one]\n"
             "    _ = (%(u)s * %(v)s * %(u)s) * %(u)s := by rw [mul_assoc (%(u)s * %(v)s)]\n    _ = %(v)s * %(u)s := by rw [h %(u)s %(v)s]") % dict(u=u, v=v, T=T)),
    }

def involution(rng, difficulty):
    T = rng.choice(TYPES); u, v = rng.choice(NAMES2)
    kinds = {1: ["self", "inveq"], 2: ["sq", "sqmul", "invmul"], 3: ["aba", "sqmul", "invmul", "sq"]}[difficulty]
    kind = rng.choice(kinds)
    hl, ht, proof = inv_hyps(T, u, v)[kind]
    concl = rng.choice(["comm"] if difficulty == 1 else ["comm", "conj", "center"])
    if concl == "comm":
        goal = "∀ %s %s : %s, %s * %s = %s * %s" % (u, v, T, u, v, v, u)
        words = "Then \\(G\\) is commutative: \\(ab = ba\\) for all \\(a, b \\in G\\)."
        final = proof
    else:
        key = "have key : ∀ %s %s : %s, %s * %s = %s * %s := %s" % (u, v, T, u, v, v, u, indent(proof, 2).lstrip())
        if concl == "conj":
            goal = "∀ %s %s : %s, %s * %s * %s⁻¹ = %s" % (u, v, T, u, v, u, v)
            words = "Then \\(a b a^{-1} = b\\) for all \\(a, b \\in G\\)."
            final = "by\n  %s\n  intro %s %s\n  rw [mul_inv_eq_iff_eq_mul]\n  exact key %s %s" % (key, u, v, u, v)
        else:
            goal = "∀ z : %s, z ∈ Subgroup.center %s" % (T, T)
            words = "Then every element of \\(G\\) lies in the center of \\(G\\)."
            final = "by\n  %s\n  intro z\n  rw [Subgroup.mem_center_iff]\n  intro g\n  exact key g z" % key
    informal = "Let \\(G\\) be a group such that \\(%s\\). %s" % (ht, words)
    ths = []
    if difficulty == 3 and concl == "comm":
        n = rng.randrange(3, 10)
        lem = Theorem("involution_comm", "{%s : Type*} [Group %s] (h : %s) :\n    %s" % (T, T, hl, goal), final, "The group is commutative.", 0.4)
        main = Theorem("power_of_product", "{%s : Type*} [Group %s] (h : %s) (%s %s : %s) :\n    (%s * %s) ^ %d = %s ^ %d * %s ^ %d" % (T, T, hl, u, v, T, u, v, n, u, n, v, n),
                       "by\n  exact Commute.mul_pow (involution_comm h %s %s) %d" % (u, v, n), "In this group \\((ab)^%d = a^%d b^%d\\)." % (n, n, n), 0.6)
        informal += " Deduce that \\((ab)^{%d} = a^{%d} b^{%d}\\) for all \\(a, b \\in G\\)." % (n, n, n)
        return informal, [lem, main]
    return informal, [Theorem("group_commutes", "{%s : Type*} [Group %s] (h : %s) :\n    %s" % (T, T, hl, goal), final,
                              "The stated consequence of the hypothesis on the group.")]

# ---------------------------------------------------------------- inverse

def perm_mul(p, q): return tuple(p[i] for i in q)       # (p * q)(i) = p(q(i))
def perm_inv(p):
    r = [0] * len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)

def cyclic(rng, difficulty):
    k = {1: 3, 2: rng.randrange(4, 7), 3: rng.randrange(6, 9)}[difficulty]
    r = rng.randrange(1, k)
    base = rng.choice(["x", "a", "g", "t"]); T = rng.choice(TYPES)
    names = [base + sub(i + 1) for i in range(k)]
    # second code path: in S_5, choose a_2..a_k at random, a_1 = (a_2...a_k)^{-1}; then the rotation is e
    for _ in range(5):
        els = [tuple(rng.sample(range(5), 5)) for _ in range(k - 1)]
        prod = tuple(range(5))
        for e in els: prod = perm_mul(prod, e)
        els = [perm_inv(prod)] + els
        full = tuple(range(5))
        for e in els: full = perm_mul(full, e)
        assert full == tuple(range(5))
        rot = els[r:] + els[:r]; res = tuple(range(5))
        for e in rot: res = perm_mul(res, e)
        assert res == tuple(range(5))
    prod_l = " * ".join(names); rot_l = " * ".join(names[r:] + names[:r])
    pre = " * ".join(names[:r])
    stmt = "{%s : Type*} [Group %s] (%s : %s)\n    (h : %s = 1) : %s = 1" % (T, T, " ".join(names), T, prod_l, rot_l)
    proof = "by\n  calc %s = (%s)⁻¹ * (%s) * (%s) := by group\n    _ = 1 := by rw [h]; group" % (rot_l, pre, prod_l, pre)
    tp = lambda ns: " ".join(n.replace(base, "a_") if False else n for n in ns)
    tex = lambda ns: " ".join("%s_{%d}" % (base, int(n[len(base):].translate(str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")))) for n in ns)
    informal = "Let \\(G\\) be a group and \\(%s \\in G\\) with \\(%s = e\\). Then \\(%s = e\\)." % (
        ", ".join("%s_{%d}" % (base, i + 1) for i in range(k)), tex(names), tex(names[r:] + names[:r]))
    return informal, [Theorem("rotate_product", stmt, proof, "A product equal to the identity stays equal to the identity after a cyclic rotation.")]

def inverse(rng, difficulty):
    kinds = {1: ["unique", "cyclic"], 2: ["cyclic", "conj", "conj", "powinv"], 3: ["right", "right", "cyclic"]}[difficulty]
    kind = rng.choice(kinds)
    if kind == "cyclic": return cyclic(rng, difficulty)
    T = rng.choice(["M", "S", "N"]); x, y, z = rng.choice(NAMES3)
    if kind == "unique":
        order = rng.choice([0, 1])
        h1, h2 = ("%s * %s = 1" % (x, y), "%s * %s = 1" % (z, x)) if order == 0 else ("%s * %s = 1" % (z, x), "%s * %s = 1" % (x, y))
        informal = "Let \\(M\\) be a monoid and \\(%s, %s, %s \\in M\\) with \\(%s %s = 1\\) and \\(%s %s = 1\\). Then \\(%s = %s\\)." % (x, y, z, x, y, z, x, y, z)
        proof = ("by\n  calc %s = (%s * %s) * %s := by rw [%s, one_mul]\n    _ = %s * (%s * %s) := mul_assoc _ _ _\n    _ = %s := by rw [%s, mul_one]" % (
            y, z, x, y, "h2" if order == 0 else "h1", z, x, y, z, "h1" if order == 0 else "h2"))
        return informal, [Theorem("inverses_agree", "{%s : Type*} [Monoid %s] (%s %s %s : %s)\n    (h1 : %s) (h2 : %s) : %s = %s" % (T, T, x, y, z, T, h1, h2, y, z), proof,
                                  "A left inverse and a right inverse of the same element are equal.")]
    if kind == "conj":
        shape = rng.choice(["conj", "invconj", "order"]); T = rng.choice(TYPES)
        if shape == "conj":
            stmt = "{%s : Type*} [Group %s] (%s %s : %s) (n : ℕ) :\n    (%s * %s * %s⁻¹) ^ n = %s * %s ^ n * %s⁻¹" % (T, T, x, y, T, x, y, x, x, y, x)
            proof = "by\n  induction n with\n  | zero => simp\n  | succ j ih =>\n    rw [pow_succ, ih]\n    group"
            informal = "Let \\(G\\) be a group, \\(%s, %s \\in G\\) and \\(n \\in \\mathbb{N}\\). Then \\((%s %s %s^{-1})^n = %s %s^n %s^{-1}\\)." % (x, y, x, y, x, x, y, x)
        elif shape == "invconj":
            stmt = "{%s : Type*} [Group %s] (%s %s : %s) (n : ℕ) :\n    (%s⁻¹ * %s * %s) ^ n = %s⁻¹ * %s ^ n * %s" % (T, T, x, y, T, x, y, x, x, y, x)
            proof = "by\n  induction n with\n  | zero => simp\n  | succ j ih =>\n    rw [pow_succ, ih]\n    group"
            informal = "Let \\(G\\) be a group, \\(%s, %s \\in G\\) and \\(n \\in \\mathbb{N}\\). Then \\((%s^{-1} %s %s)^n = %s^{-1} %s^n %s\\)." % (x, y, x, y, x, x, y, x)
        else:
            stmt = "{%s : Type*} [Group %s] (%s %s : %s) :\n    orderOf (%s * %s * %s⁻¹) = orderOf %s" % (T, T, x, y, T, x, y, x, y)
            proof = "by\n  exact orderOf_injective (MulAut.conj %s).toMonoidHom (MulAut.conj %s).injective %s" % (x, x, y)
            informal = "Let \\(G\\) be a group and \\(%s, %s \\in G\\). Then the order of \\(%s %s %s^{-1}\\) equals the order of \\(%s\\) (orders are in \\(\\mathbb{N}\\), with 0 meaning infinite order)." % (x, y, x, y, x, y)
        return informal, [Theorem("conjugate_fact", stmt, proof, "A fact about conjugation and powers.")]
    if kind == "powinv":
        T = rng.choice(["M", "S"])
        proof = ("by\n  induction n with\n  | zero => simp\n  | succ j ih =>\n    calc %(x)s ^ (j + 1) * %(y)s ^ (j + 1) = %(x)s ^ j * (%(x)s * %(y)s) * %(y)s ^ j := by rw [pow_succ, pow_succ']; simp only [mul_assoc]\n"
                 "      _ = 1 := by rw [h, mul_one]; exact ih") % dict(x=x, y=y)
        informal = "Let \\(M\\) be a monoid and \\(%s, %s \\in M\\) with \\(%s %s = 1\\). Then \\(%s^n %s^n = 1\\) for every \\(n \\in \\mathbb{N}\\)." % (x, y, x, y, x, y)
        return informal, [Theorem("pow_pair_one", "{%s : Type*} [Monoid %s] (%s %s : %s) (h : %s * %s = 1) (n : ℕ) :\n    %s ^ n * %s ^ n = 1" % (T, T, x, y, T, x, y, x, y), proof,
                                  "If xy = 1 then x^n y^n = 1.")]
    # right: elements with a right inverse are invertible on both sides
    left = rng.choice([0, 1])
    hh = "∀ %s : %s, ∃ %s, %s * %s = 1" % (x, T, y, x, y) if left == 0 else "∀ %s : %s, ∃ %s, %s * %s = 1" % (x, T, y, y, x)
    if left == 0:
        goal = "∀ %s %s : %s, %s * %s = 1 → %s * %s = 1" % (x, y, T, x, y, y, x)
        proof = ("by\n  intro %s %s hxy\n  obtain ⟨%s, hyz⟩ := h %s\n  calc %s * %s = %s * %s * (%s * %s) := by rw [hyz, mul_one]\n    _ = %s * (%s * %s) * %s := by simp only [mul_assoc]\n    _ = %s * %s := by rw [hxy, mul_one]\n    _ = 1 := hyz" % (
            x, y, z, y, y, x, y, x, y, z, y, x, y, z, y, z))
        informal = "Let \\(M\\) be a monoid in which every element \\(x\\) has some \\(y\\) with \\(xy = 1\\). Then \\(xy = 1\\) implies \\(yx = 1\\) for all \\(x, y \\in M\\)."
        main_stmt = "{%s : Type*} [Monoid %s] (h : %s) (%s %s %s : %s)\n    (h1 : %s * %s = 1) (h2 : %s * %s = 1) : %s = %s" % (T, T, hh, x, y, z, T, x, y, x, z, y, z)
        main_proof = "by\n  have hyx := right_inverse_comm h %s %s h1\n  calc %s = %s * (%s * %s) := by rw [h2, mul_one]\n    _ = (%s * %s) * %s := (mul_assoc _ _ _).symm\n    _ = %s := by rw [hyx, one_mul]" % (x, y, y, y, x, z, y, x, z, z)
        main_inf = "Under the same hypothesis, if \\(%s %s = 1\\) and \\(%s %s = 1\\) then \\(%s = %s\\)." % (x, y, x, z, y, z)
    else:
        goal = "∀ %s %s : %s, %s * %s = 1 → %s * %s = 1" % (x, y, T, y, x, x, y)
        proof = ("by\n  intro %s %s hyx\n  obtain ⟨%s, hzy⟩ := h %s\n  have hzx : %s = %s := by\n    calc %s = %s * (%s * %s) := by rw [hyx, mul_one]\n      _ = (%s * %s) * %s := (mul_assoc _ _ _).symm\n      _ = %s := by rw [hzy, one_mul]\n  rw [← hzx]\n  exact hzy" % (
            x, y, z, y, z, x, z, z, y, x, z, y, x, x))
        informal = "Let \\(M\\) be a monoid in which every element \\(x\\) has some \\(y\\) with \\(yx = 1\\). Then \\(yx = 1\\) implies \\(xy = 1\\) for all \\(x, y \\in M\\)."
        main_stmt = "{%s : Type*} [Monoid %s] (h : %s) (%s %s %s : %s)\n    (h1 : %s * %s = 1) (h2 : %s * %s = 1) : %s = %s" % (T, T, hh, x, y, z, T, y, x, z, x, y, z)
        main_proof = ("by\n  have hxy := right_inverse_comm h %s %s h1\n  calc %s = (%s * %s) * %s := by rw [h2, one_mul]\n    _ = %s * (%s * %s) := mul_assoc _ _ _\n    _ = %s := by rw [hxy, mul_one]") % (
            x, y, y, z, x, y, z, x, y, z)
        main_inf = "Under the same hypothesis, if \\(%s %s = 1\\) and \\(%s %s = 1\\) then \\(%s = %s\\)." % (y, x, z, x, y, z)
    lem = Theorem("right_inverse_comm", "{%s : Type*} [Monoid %s] (h : %s) :\n    %s" % (T, T, hh, goal), proof, "One-sided inverses are two-sided.", 0.4)
    main = Theorem("inverse_unique", main_stmt, main_proof, "The inverse is unique.", 0.6)
    return informal + " " + main_inf, [lem, main]

# ---------------------------------------------------------------- subgroup

def member(rng, difficulty, S, names):
    """A random product of elements of the subgroup S. Returns (Lean expression, TeX, proof term)."""
    k = {1: rng.randrange(2, 4), 2: rng.randrange(4, 6), 3: 5}[difficulty]
    facs = []
    for i in range(k):
        n = names[i % len(names)]
        form = rng.choice(["plain", "inv", "pow"] if difficulty > 1 else ["plain", "inv"])
        facs.append((n, form, rng.randrange(2, 6)))
    def fl(f): return f[0] if f[1] == "plain" else (f[0] + "⁻¹" if f[1] == "inv" else "%s ^ %d" % (f[0], f[2]))
    def ft(f): return f[0] if f[1] == "plain" else (f[0] + "^{-1}" if f[1] == "inv" else "%s^{%d}" % (f[0], f[2]))
    def fp(f): return "h" + f[0] if f[1] == "plain" else ("(inv_mem h%s)" % f[0] if f[1] == "inv" else "(pow_mem h%s %d)" % (f[0], f[2]))
    expr = " * ".join(fl(f) for f in facs); tex = " ".join(ft(f) for f in facs)
    proof = fp(facs[0])
    for f in facs[1:]: proof = "(mul_mem %s %s)" % (proof, fp(f))
    if proof.startswith("(") and len(facs) > 1: proof = proof[1:-1]
    return expr, tex, proof, sorted({f[0] for f in facs})

def lagrange_numbers(rng, difficulty):
    m = rng.choice([2, 3, 4, 5, 6, 8, 9, 10]); k = rng.choice([2, 3, 4, 5, 6, 7]); n = m * k
    assert Nat_card_check(m, k, n)
    return m, k, n
def Nat_card_check(m, k, n): return m * k == n and n % m == 0 and n // m == k

def subgroup(rng, difficulty):
    T = rng.choice(TYPES)
    kinds = {1: ["member"], 2: ["normal", "lagrange", "index"], 3: ["union", "union2", "prime", "index"]}[difficulty]
    kind = rng.choice(kinds)
    S = rng.choice(["H", "K", "N", "L"]); names = list(rng.choice(NAMES3))
    if kind == "member":
        expr, tex, pr, used = member(rng, difficulty, S, names)
        binders = " ".join(used)
        hyps = " ".join("(h%s : %s ∈ %s)" % (n, n, S) for n in used)
        informal = "Let \\(%s\\) be a subgroup of a group \\(G\\) and let %s lie in \\(%s\\). Then \\(%s \\in %s\\)." % (S, ", ".join("\\(%s\\)" % n for n in used), S, tex, S)
        return informal, [Theorem("product_mem", "{%s : Type*} [Group %s] (%s : Subgroup %s) {%s : %s}\n    %s : %s ∈ %s" % (T, T, S, T, binders, T, hyps, expr, S), "by\n  exact " + pr,
                                  "A product of elements of a subgroup, with inverses and powers, lies in the subgroup.")]
    if kind == "normal":
        x, g = names[0], names[1]; n = rng.randrange(2, 8); shape = rng.choice(["pow", "comm"])
        if shape == "pow":
            goal = "%s * %s ^ %d * %s⁻¹ ∈ %s" % (g, x, n, g, S); pr = "hN.conj_mem _ (pow_mem hx %d) %s" % (n, g)
            words = "\\(%s %s^{%d} %s^{-1} \\in %s\\)" % (g, x, n, g, S)
        else:
            goal = "%s * %s * %s⁻¹ * %s⁻¹ ∈ %s" % (g, x, g, x, S); pr = "mul_mem (hN.conj_mem _ hx %s) (inv_mem hx)" % g
            words = "\\(%s %s %s^{-1} %s^{-1} \\in %s\\)" % (g, x, g, x, S)
        informal = "Let \\(%s\\) be a normal subgroup of a group \\(G\\), let \\(%s \\in %s\\) and \\(%s \\in G\\). Then %s." % (S, x, S, g, words)
        return informal, [Theorem("normal_conj", "{%s : Type*} [Group %s] (%s : Subgroup %s) (hN : %s.Normal) {%s : %s} (hx : %s ∈ %s) (%s : %s) :\n    %s" % (T, T, S, T, S, x, T, x, S, g, T, goal),
                                  "by\n  exact " + pr, "Conjugates of elements of a normal subgroup stay in it.")]
    if kind == "lagrange":
        m, k, n = lagrange_numbers(rng, difficulty); n_ord = n
        shape = rng.choice(["card", "order"])
        if shape == "card":
            informal = "Let \\(G\\) be a group with \\(|G| = %d\\) and \\(%s\\) a subgroup of \\(G\\). Then \\(|%s|\\) divides %d." % (n, S, S, n)
            return informal, [Theorem("subgroup_card_dvd", "{%s : Type*} [Group %s] (hG : Nat.card %s = %d) (%s : Subgroup %s) :\n    Nat.card %s ∣ %d" % (T, T, T, n, S, T, S, n),
                                      "by\n  rw [← hG]\n  exact Subgroup.card_subgroup_dvd_card %s" % S, "Lagrange: the order of a subgroup divides the order of the group.")]
        informal = "Let \\(G\\) be a group with \\(|G| = %d\\) and \\(%s \\in G\\). Then the order of \\(%s\\) divides %d." % (n, names[0], names[0], n)
        return informal, [Theorem("order_dvd", "{%s : Type*} [Group %s] (hG : Nat.card %s = %d) (%s : %s) :\n    orderOf %s ∣ %d" % (T, T, T, n, names[0], T, names[0], n),
                                  "by\n  rw [← hG]\n  exact orderOf_dvd_natCard %s" % names[0], "The order of an element divides the order of the group.")]
    if kind == "index":
        m, k, n = lagrange_numbers(rng, difficulty)
        informal = "Let \\(G\\) be a group with \\(|G| = %d\\) and \\(%s\\) a subgroup with \\(|%s| = %d\\). Then \\(%s\\) has index %d in \\(G\\)." % (n, S, S, m, S, k)
        return informal, [Theorem("subgroup_index", "{%s : Type*} [Group %s] (hG : Nat.card %s = %d) (%s : Subgroup %s) (hH : Nat.card %s = %d) :\n    %s.index = %d" % (T, T, T, n, S, T, S, m, S, k),
                                  "by\n  have h := Subgroup.card_mul_index %s\n  rw [hG, hH] at h\n  omega" % S, "Lagrange: the cardinality is the product of subgroup order and index.")]
    if kind in ("union", "union2"):
        A, B = rng.choice([("H", "K"), ("A", "B"), ("P", "R")])
        if kind == "union":
            hyp = "∀ a b : %s, (a ∈ %s ∨ a ∈ %s) → (b ∈ %s ∨ b ∈ %s) → (a * b ∈ %s ∨ a * b ∈ %s)" % (T, A, B, A, B, A, B)
            use = "h a b (Or.inl haH) (Or.inr hbK)"
            words = "whenever \\(a\\) and \\(b\\) each lie in \\(%s\\) or in \\(%s\\), the product \\(ab\\) lies in \\(%s\\) or in \\(%s\\)" % (A, B, A, B)
        else:
            hyp = "∀ a ∈ %s, ∀ b ∈ %s, a * b ∈ %s ∨ a * b ∈ %s" % (A, B, A, B)
            use = "h a haH b hbK"
            words = "for all \\(a \\in %s\\) and \\(b \\in %s\\) the product \\(ab\\) lies in \\(%s\\) or in \\(%s\\)" % (A, B, A, B)
        stmt = "{%s : Type*} [Group %s] (%s %s : Subgroup %s)\n    (h : %s) : %s ≤ %s ∨ %s ≤ %s" % (T, T, A, B, T, hyp, A, B, B, A)
        proof = ("by\n  by_contra hcon\n  rw [not_or] at hcon\n  obtain ⟨h1, h2⟩ := hcon\n  rw [SetLike.not_le_iff_exists] at h1 h2\n"
                 "  obtain ⟨a, haH, haK⟩ := h1\n  obtain ⟨b, hbK, hbH⟩ := h2\n  rcases %s with hab | hab\n"
                 "  · exact hbH (by simpa using mul_mem (inv_mem haH) hab)\n  · exact haK (by simpa using mul_mem hab (inv_mem hbK))") % use
        informal = "Let \\(%s\\) and \\(%s\\) be subgroups of a group \\(G\\) such that %s. Then \\(%s \\subseteq %s\\) or \\(%s \\subseteq %s\\)." % (A, B, words, A, B, B, A)
        return informal, [Theorem("subgroup_union", stmt, proof, "A product-closed union of two subgroups is one of them.")]
    # prime
    p = rng.choice([3, 5, 7, 11, 13, 17, 19])
    assert all(p % d for d in range(2, p))
    g = names[0]
    informal = "Let \\(G\\) be a group with \\(|G| = %d\\). Then \\(x^{%d} = e\\) for every \\(x \\in G\\), and every element \\(%s \\neq e\\) has order exactly %d." % (p, p, g, p)
    lem = Theorem("pow_card", "{%s : Type*} [Group %s] (hG : Nat.card %s = %d) (x : %s) :\n    x ^ %d = 1" % (T, T, T, p, T, p), "by\n  rw [← hG]\n  exact pow_card_eq_one'", "Every element satisfies x^|G| = 1.", 0.4)
    main = Theorem("order_prime", "{%s : Type*} [Group %s] (hG : Nat.card %s = %d) (%s : %s) (hne : %s ≠ 1) :\n    orderOf %s = %d" % (T, T, T, p, g, T, g, g, p),
                   "by\n  haveI : Fact (Nat.Prime %d) := ⟨by norm_num⟩\n  exact orderOf_eq_prime (pow_card %s %s) hne" % (p, "hG", g), "In a group of prime order p, every non-identity element has order p.", 0.6)
    return informal, [lem, main]

# ---------------------------------------------------------------- hom

def hom(rng, difficulty):
    G, H = rng.choice([("G", "H"), ("A", "B"), ("G", "K"), ("X", "Y")])
    x, y = rng.choice(NAMES2)
    kinds = {1: ["prod", "pow", "inv", "normal"], 2: ["inj", "comp", "inj", "comp"], 3: ["injcomp", "inj", "cardinj", "range"]}[difficulty]
    kind = rng.choice(kinds)
    pre = "{%s %s : Type*} [Group %s] [Group %s] (f : %s →* %s)" % (G, H, G, H, G, H)
    if kind == "prod":
        informal = "Let \\(f : G \\to H\\) be a group homomorphism and \\(%s, %s\\) in its kernel. Then \\(%s %s^{-1}\\) lies in the kernel." % (x, y, x, y)
        return informal, [Theorem("kernel_mul_inv", "%s {%s %s : %s}\n    (hx : %s ∈ f.ker) (hy : %s ∈ f.ker) : %s * %s⁻¹ ∈ f.ker" % (pre, x, y, G, x, y, x, y), "by\n  exact mul_mem hx (inv_mem hy)",
                                  "The kernel is closed under x y⁻¹.")]
    if kind == "pow":
        n = rng.randrange(2, 12)
        informal = "Let \\(f : G \\to H\\) be a group homomorphism and \\(%s\\) an element of \\(G\\) with \\(f(%s) = e\\). Then \\(f(%s^{%d}) = e\\)." % (x, x, x, n)
        return informal, [Theorem("image_of_power", "%s (%s : %s)\n    (hx : f %s = 1) : f (%s ^ %d) = 1" % (pre, x, G, x, x, n), "by\n  rw [map_pow, hx, one_pow]", "Powers of kernel elements are in the kernel.")]
    if kind == "inv":
        informal = "Let \\(f : G \\to H\\) be a group homomorphism and \\(%s, %s \\in G\\). Then \\(f(%s) = f(%s)\\) if and only if \\(%s^{-1} %s\\) lies in the kernel of \\(f\\)." % (x, y, x, y, x, y)
        return informal, [Theorem("eq_iff_mem_ker", "%s (%s %s : %s) :\n    f %s = f %s ↔ %s⁻¹ * %s ∈ f.ker" % (pre, x, y, G, x, y, x, y),
                                  "by\n  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]", "Two elements have the same image exactly when x⁻¹ y is in the kernel.")]
    if kind == "conj":
        n = rng.randrange(1, 6)
        informal = "Let \\(f : G \\to H\\) be a group homomorphism, \\(%s \\in G\\) with \\(f(%s) = e\\) and \\(%s \\in G\\). Then \\(f(%s %s^{%d} %s^{-1}) = e\\)." % (x, x, y, y, x, n, y)
        return informal, [Theorem("conj_in_kernel", "%s (%s %s : %s)\n    (hx : f %s = 1) : f (%s * %s ^ %d * %s⁻¹) = 1" % (pre, x, y, G, x, y, x, n, y),
                                  "by\n  rw [map_mul, map_mul, map_pow, map_inv, hx, one_pow, mul_one, mul_inv_cancel]", "The kernel is normal.")]
    if kind == "normal":
        informal = "Let \\(f : G \\to H\\) be a group homomorphism and \\(%s, %s \\in G\\) with \\(f(%s) = e\\). Then \\(%s %s %s^{-1} %s^{-1}\\) lies in the kernel of \\(f\\)." % (x, y, x, y, x, y, x)
        return informal, [Theorem("commutator_in_kernel", "%s (%s %s : %s)\n    (hx : f %s = 1) : %s * %s * %s⁻¹ * %s⁻¹ ∈ f.ker" % (pre, x, y, G, x, y, x, y, x),
                                  "by\n  exact mul_mem (f.normal_ker.conj_mem _ hx %s) (inv_mem hx)" % y, "Commutators with a kernel element lie in the kernel.")]
    if kind == "inj":
        informal = "Let \\(f : G \\to H\\) be a group homomorphism such that \\(f(%s) = e\\) implies \\(%s = e\\) for every \\(%s \\in G\\). Then \\(f\\) is injective." % (x, x, x)
        return informal, [Theorem("injective_of_trivial_kernel", "%s\n    (h : ∀ %s : %s, f %s = 1 → %s = 1) : Function.Injective f" % (pre, x, G, x, x),
                                  "by\n  intro a b hab\n  have h1 : f (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]\n  exact inv_mul_eq_one.mp (h _ h1)",
                                  "A homomorphism with trivial kernel is injective.")]
    if kind == "comp":
        K = "Z"
        informal = "Let \\(f : G \\to H\\) and \\(g : H \\to K\\) be group homomorphisms. Then every element of the kernel of \\(f\\) lies in the kernel of \\(g \\circ f\\)."
        return informal, [Theorem("ker_le_ker_comp", "{%s %s %s : Type*} [Group %s] [Group %s] [Group %s] (f : %s →* %s) (g : %s →* %s) :\n    f.ker ≤ (g.comp f).ker" % (G, H, K, G, H, K, G, H, H, K),
                                  "by\n  intro %s hx\n  rw [MonoidHom.mem_ker] at hx ⊢\n  rw [MonoidHom.comp_apply, hx, map_one]" % x, "The kernel of f lies in the kernel of g after f.")]
    if kind == "injcomp":
        K = "Z"
        informal = "Let \\(f : G \\to H\\) and \\(g : H \\to K\\) be group homomorphisms with \\(g\\) injective. Then \\(g \\circ f\\) and \\(f\\) have the same kernel."
        lem = Theorem("ker_le_ker_comp", "{%s %s %s : Type*} [Group %s] [Group %s] [Group %s] (f : %s →* %s) (g : %s →* %s) :\n    f.ker ≤ (g.comp f).ker" % (G, H, K, G, H, K, G, H, H, K),
                      "by\n  intro %s hx\n  rw [MonoidHom.mem_ker] at hx ⊢\n  rw [MonoidHom.comp_apply, hx, map_one]" % x, "The kernel of f lies in the kernel of g after f.", 0.3)
        main = Theorem("ker_comp_eq", "{%s %s %s : Type*} [Group %s] [Group %s] [Group %s] (f : %s →* %s) (g : %s →* %s)\n    (hg : Function.Injective g) : (g.comp f).ker = f.ker" % (G, H, K, G, H, K, G, H, H, K),
                       "by\n  apply le_antisymm\n  · intro %s hx\n    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx\n    rw [MonoidHom.mem_ker]\n    exact hg (by rw [hx, map_one])\n  · exact ker_le_ker_comp f g" % x,
                       "If g is injective the kernels agree.", 0.7)
        return informal + " Show that \\(\\ker f \\subseteq \\ker(g \\circ f)\\) and then the equality.", [lem, main]
    if kind == "cardinj":
        informal = "Let \\(f : G \\to H\\) be a group homomorphism whose kernel has exactly one element. Then \\(f\\) is injective."
        return informal, [Theorem("injective_of_card_ker", "%s\n    (h : Nat.card f.ker = 1) : Function.Injective f" % pre, "by\n  exact (MonoidHom.ker_eq_bot_iff f).mp (Subgroup.card_eq_one.mp h)",
                                  "A homomorphism whose kernel has one element is injective.")]
    # range: an injective hom from G into H gives |G| dividing |H|
    informal = "Let \\(f : G \\to H\\) be an injective group homomorphism of groups. Then \\(|G|\\) divides \\(|H|\\) (cardinalities are in \\(\\mathbb{N}\\), with 0 for an infinite group)."
    return informal, [Theorem("card_dvd_of_injective", "%s\n    (hf : Function.Injective f) : Nat.card %s ∣ Nat.card %s" % (pre, G, H),
                              "by\n  have h1 : Nat.card %s = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv\n  rw [h1]\n  exact Subgroup.card_subgroup_dvd_card f.range" % G,
                              "Lagrange for an injective homomorphism.")]

FAM = {"involution": involution, "inverse": inverse, "subgroup": subgroup, "hom": hom}
TITLES = {"involution": "Commutativity from a group law", "inverse": "Inverses and cancellation", "subgroup": "Subgroups and their orders", "hom": "Kernels of group homomorphisms"}

def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    informal, theorems = FAM[family](rng, difficulty)
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove",
        title=TITLES[family], informal="Prove the following statement.\n\n" + informal, theorems=theorems)
