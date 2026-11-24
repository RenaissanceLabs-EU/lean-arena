"""Logic and set algebra (MSC 03: mathematical logic and foundations; 03B, 03E).

Families: predicate-logic equivalences; set identities over `Set α` proved by extensionality (algebra at
difficulties 1 and 3, images and preimages at 2 and sometimes 3);
cardinality facts on `Finset ℕ`; equivalence relations on integers and pairs.
Second code path: every set identity is checked on a truth table (membership of one element in
each variable set) in Python before it is returned, including the rows allowed by a hypothesis.
"""
import itertools
from arena.core import Task, Theorem, rng_for

ENV = "logic_and_sets"
# `quantifiers` is retired: aesop closes every task in it, so it teaches nothing. The generator stays for tests.
FAMILIES = ["finset_card", "relations", "set_identities"]

# ---------------------------------------------------------------- quantifiers
# Each item: (needs_nonempty, uses_prop, statement body, tex, proof). Placeholders: %(P)s %(Q)s %(R)s %(c)s.
Q1 = [
    (False, False, "(¬ ∀ x, %(P)s x) ↔ ∃ x, ¬ %(P)s x", "\\neg \\forall x\\, %(P)s(x) \\iff \\exists x\\, \\neg %(P)s(x)",
     "by\n  constructor\n  · intro h\n    by_contra h'\n    apply h\n    intro x\n    by_contra hx\n    exact h' ⟨x, hx⟩\n  · rintro ⟨x, hx⟩ h\n    exact hx (h x)"),
    (False, False, "(¬ ∃ x, %(P)s x) ↔ ∀ x, ¬ %(P)s x", "\\neg \\exists x\\, %(P)s(x) \\iff \\forall x\\, \\neg %(P)s(x)",
     "by\n  constructor\n  · intro h x hx\n    exact h ⟨x, hx⟩\n  · rintro h ⟨x, hx⟩\n    exact h x hx"),
    (False, False, "(∀ x, %(P)s x ∧ %(Q)s x) ↔ (∀ x, %(P)s x) ∧ ∀ x, %(Q)s x", "\\forall x\\, (%(P)s(x) \\wedge %(Q)s(x)) \\iff (\\forall x\\, %(P)s(x)) \\wedge (\\forall x\\, %(Q)s(x))",
     "⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.1 x, h.2 x⟩⟩"),
    (False, False, "(∃ x, %(P)s x ∨ %(Q)s x) ↔ (∃ x, %(P)s x) ∨ ∃ x, %(Q)s x", "\\exists x\\, (%(P)s(x) \\vee %(Q)s(x)) \\iff (\\exists x\\, %(P)s(x)) \\vee (\\exists x\\, %(Q)s(x))",
     "by\n  constructor\n  · rintro ⟨x, hx | hx⟩\n    · exact Or.inl ⟨x, hx⟩\n    · exact Or.inr ⟨x, hx⟩\n  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)\n    · exact ⟨x, Or.inl hx⟩\n    · exact ⟨x, Or.inr hx⟩"),
]
Q2 = [
    (True, True, "(∃ x, %(P)s x → %(c)s) ↔ ((∀ x, %(P)s x) → %(c)s)", "\\exists x\\, (%(P)s(x) \\to %(c)s) \\iff ((\\forall x\\, %(P)s(x)) \\to %(c)s)",
     "by\n  constructor\n  · rintro ⟨x, hx⟩ h\n    exact hx (h x)\n  · intro h\n    by_cases hall : ∀ x, %(P)s x\n    · exact ⟨Classical.arbitrary _, fun _ => h hall⟩\n    · push_neg at hall\n      obtain ⟨x, hx⟩ := hall\n      exact ⟨x, fun hp => absurd hp hx⟩"),
    (False, False, "(¬ ∀ x, %(P)s x → %(Q)s x) ↔ ∃ x, %(P)s x ∧ ¬ %(Q)s x", "\\neg \\forall x\\, (%(P)s(x) \\to %(Q)s(x)) \\iff \\exists x\\, (%(P)s(x) \\wedge \\neg %(Q)s(x))",
     "by\n  constructor\n  · intro h\n    by_contra h'\n    apply h\n    intro x hp\n    by_contra hq\n    exact h' ⟨x, hp, hq⟩\n  · rintro ⟨x, hp, hq⟩ h\n    exact hq (h x hp)"),
    (False, True, "(∀ x, %(P)s x ∨ %(c)s) ↔ (∀ x, %(P)s x) ∨ %(c)s", "\\forall x\\, (%(P)s(x) \\vee %(c)s) \\iff (\\forall x\\, %(P)s(x)) \\vee %(c)s",
     "by\n  constructor\n  · intro h\n    by_cases hc : %(c)s\n    · exact Or.inr hc\n    · exact Or.inl fun x => (h x).resolve_right hc\n  · rintro (h | h) x\n    · exact Or.inl (h x)\n    · exact Or.inr h"),
    (False, True, "(∀ x, %(P)s x → %(c)s) ↔ ((∃ x, %(P)s x) → %(c)s)", "\\forall x\\, (%(P)s(x) \\to %(c)s) \\iff ((\\exists x\\, %(P)s(x)) \\to %(c)s)",
     "⟨fun h ⟨x, hx⟩ => h x hx, fun h x hx => h ⟨x, hx⟩⟩"),
    (False, False, "(∀ x, (%(P)s x ↔ %(Q)s x)) → ((∃ x, %(P)s x) ↔ ∃ x, %(Q)s x)", "(\\forall x\\, (%(P)s(x) \\iff %(Q)s(x))) \\to ((\\exists x\\, %(P)s(x)) \\iff (\\exists x\\, %(Q)s(x)))",
     "by\n  intro h\n  constructor\n  · rintro ⟨x, hx⟩\n    exact ⟨x, (h x).1 hx⟩\n  · rintro ⟨x, hx⟩\n    exact ⟨x, (h x).2 hx⟩"),
]
Q3 = [
    (True, False, "∃ x, %(P)s x → ∀ y, %(P)s y", "\\exists x\\, (%(P)s(x) \\to \\forall y\\, %(P)s(y))",
     "by\n  by_cases h : ∀ y, %(P)s y\n  · exact ⟨Classical.arbitrary _, fun _ => h⟩\n  · push_neg at h\n    obtain ⟨x, hx⟩ := h\n    exact ⟨x, fun hp => absurd hp hx⟩"),
    (False, False, "¬ ∃ x, ∀ y, (%(R)s x y ↔ ¬ %(R)s y y)", "\\neg \\exists x\\, \\forall y\\, (%(R)s(x, y) \\iff \\neg %(R)s(y, y))",
     "by\n  rintro ⟨x, hx⟩\n  have h := hx x\n  tauto"),
    (False, False, "(¬ ∃ x, ∀ y, %(R)s x y) ↔ ∀ x, ∃ y, ¬ %(R)s x y", "\\neg \\exists x\\, \\forall y\\, %(R)s(x, y) \\iff \\forall x\\, \\exists y\\, \\neg %(R)s(x, y)",
     "by\n  constructor\n  · intro h x\n    by_contra h'\n    apply h\n    refine ⟨x, fun y => ?_⟩\n    by_contra hy\n    exact h' ⟨y, hy⟩\n  · rintro h ⟨x, hx⟩\n    obtain ⟨y, hy⟩ := h x\n    exact hy (hx y)"),
    (False, False, "(∃ x, %(P)s x ∧ ∀ y, %(P)s y → %(R)s x y) → ∀ y, %(P)s y → ∃ x, %(P)s x ∧ %(R)s x y", "(\\exists x\\, (%(P)s(x) \\wedge \\forall y\\, (%(P)s(y) \\to %(R)s(x, y)))) \\to \\forall y\\, (%(P)s(y) \\to \\exists x\\, (%(P)s(x) \\wedge %(R)s(x, y)))",
     "by\n  rintro ⟨x, hx, h⟩ y hy\n  exact ⟨x, hx, h y hy⟩"),
    (False, False, "((∀ x, %(P)s x → %(Q)s x) ∧ ∃ x, %(P)s x ∧ %(R)s x x) → ∃ x, %(Q)s x ∧ %(R)s x x", "((\\forall x\\, (%(P)s(x) \\to %(Q)s(x))) \\wedge \\exists x\\, (%(P)s(x) \\wedge %(R)s(x, x))) \\to \\exists x\\, (%(Q)s(x) \\wedge %(R)s(x, x))",
     "by\n  rintro ⟨h, x, hp, hr⟩\n  exact ⟨x, h x hp, hr⟩"),
    (True, False, "(∃ x, ∀ y, %(R)s x y) ∨ (∀ x, ∃ y, ¬ %(R)s x y)", "(\\exists x\\, \\forall y\\, %(R)s(x, y)) \\vee (\\forall x\\, \\exists y\\, \\neg %(R)s(x, y))",
     "by\n  by_cases h : ∃ x, ∀ y, %(R)s x y\n  · exact Or.inl h\n  · right\n    intro x\n    by_contra h'\n    apply h\n    refine ⟨x, fun y => ?_⟩\n    by_contra hy\n    exact h' ⟨y, hy⟩"),
]

def quantifiers(rng, difficulty):
    pool = {1: Q1, 2: Q2, 3: Q3}[difficulty]
    nonempty, useprop, body, tex, proof = rng.choice(pool)
    P, Q = rng.sample(["P", "Q", "S", "T"], 2)
    R = rng.choice(["R", "r", "E", "L"])
    c = rng.choice(["p", "q", "r2"]) if useprop else ""
    sub = {"P": P, "Q": Q, "R": R, "c": c}
    uses_R = "%(R)s" in body; uses_Q = "%(Q)s" in body
    binders = ["{α : Type*}"] + (["[Nonempty α]"] if nonempty else [])
    binders.append("(%s : α → Prop)" % P if not uses_Q else "(%s %s : α → Prop)" % (P, Q))
    if uses_R: binders[-1] = (binders[-1] + " (%s : α → α → Prop)" % R) if "%(P)s" in body else "(%s : α → α → Prop)" % R
    if useprop: binders.append("(%s : Prop)" % c)
    stmt = " ".join(binders) + " :\n    " + body % sub
    words = []
    if "%(P)s" in body: words.append("\\(%s\\)%s" % (P, " and \\(%s\\)" % Q if uses_Q else ""))
    pred_names = [P] + ([Q] if uses_Q else []) if "%(P)s" in body else []
    info = "Let \\(\\alpha\\) be a type" + (" (nonempty)" if nonempty else "")
    parts = []
    if pred_names: parts.append(" and ".join("\\(%s\\)" % n for n in pred_names) + (" predicates" if len(pred_names) > 1 else " a predicate") + " on \\(\\alpha\\)")
    if uses_R: parts.append("\\(%s\\) a binary relation on \\(\\alpha\\)" % R)
    if useprop: parts.append("\\(%s\\) a proposition" % c)
    info += ", " + ", ".join(parts) + ". Prove \\[%s.\\]" % (tex % sub)
    thm = "pred_logic"
    return info, [Theorem(thm, stmt, proof % sub, "The stated statement of predicate logic.")]

# ---------------------------------------------------------------- set identities
SIMP = "simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Set.mem_compl_iff]"

# Laws: (lhs, rhs) over metavariables a, b, c.
V = lambda n: ("v", n)
LAWS = [
    (("c", ("u", V("a"), V("b"))), ("i", ("c", V("a")), ("c", V("b")))),
    (("c", ("i", V("a"), V("b"))), ("u", ("c", V("a")), ("c", V("b")))),
    (("i", V("a"), ("u", V("b"), V("c"))), ("u", ("i", V("a"), V("b")), ("i", V("a"), V("c")))),
    (("u", V("a"), ("i", V("b"), V("c"))), ("i", ("u", V("a"), V("b")), ("u", V("a"), V("c")))),
    (("d", V("a"), ("u", V("b"), V("c"))), ("i", ("d", V("a"), V("b")), ("d", V("a"), V("c")))),
    (("d", V("a"), ("i", V("b"), V("c"))), ("u", ("d", V("a"), V("b")), ("d", V("a"), V("c")))),
    (("d", ("u", V("a"), V("b")), V("c")), ("u", ("d", V("a"), V("c")), ("d", V("b"), V("c")))),
    (("d", V("a"), ("d", V("b"), V("c"))), ("u", ("d", V("a"), V("b")), ("i", V("a"), V("c")))),
    (("d", V("a"), V("b")), ("i", V("a"), ("c", V("b")))),
    (("c", ("d", V("a"), V("b"))), ("u", ("c", V("a")), V("b"))),
    (("u", V("a"), ("i", V("a"), V("b"))), V("a")),
    (("u", ("d", V("a"), V("b")), ("d", V("b"), V("a"))), ("d", ("u", V("a"), V("b")), ("i", V("a"), V("b")))),
    (("i", ("d", V("a"), V("b")), ("d", V("a"), V("c"))), ("d", V("a"), ("u", V("b"), V("c")))),
]

def subst(e, m):
    if e[0] == "v": return m[e[1]]
    return (e[0],) + tuple(subst(x, m) for x in e[1:])

def ev(e, env):
    if e[0] == "v": return env[e[1]]
    if e[0] == "c": return not ev(e[1], env)
    a, b = ev(e[1], env), ev(e[2], env)
    return {"u": a or b, "i": a and b, "d": a and not b}[e[0]]

def lean(e, top=False):
    if e[0] == "v": return e[1]
    if e[0] == "c":
        return "%sᶜ" % (lean(e[1]) if e[1][0] in ("v", "c") else "(%s)" % lean(e[1], True))
    s = "%s %s %s" % (lean(e[1]), {"u": "∪", "i": "∩", "d": "\\"}[e[0]], lean(e[2]))
    return s if top else "(%s)" % s

def tex(e, top=False):
    if e[0] == "v": return e[1]
    if e[0] == "c":
        return "%s^{c}" % (tex(e[1]) if e[1][0] in ("v", "c") else "(%s)" % tex(e[1], True))
    s = "%s %s %s" % (tex(e[1]), {"u": "\\cup", "i": "\\cap", "d": "\\setminus"}[e[0]], tex(e[2]))
    return s if top else "(%s)" % s

def degenerate(e):
    if e[0] == "v": return False
    if e[0] == "c": return e[1][0] == "c" or degenerate(e[1])
    return e[1] == e[2] or degenerate(e[1]) or degenerate(e[2])

def count_vars(e, acc=None):
    acc = {} if acc is None else acc
    if e[0] == "v": acc[e[1]] = acc.get(e[1], 0) + 1
    else:
        for x in e[1:]: count_vars(x, acc)
    return acc

def vars_of(e): return {e[1]} if e[0] == "v" else set().union(*[vars_of(x) for x in e[1:]])
def size(e): return 1 if e[0] == "v" else 1 + sum(size(x) for x in e[1:])

def rand_expr(rng, depth, names):
    if depth == 0 or (depth < 3 and rng.random() < 0.3): return ("v", rng.choice(names))
    op = rng.choice(["u", "i", "d", "u", "i", "c"])
    if op == "c": return ("c", rand_expr(rng, depth - 1, names))
    return (op, rand_expr(rng, depth - 1, names), rand_expr(rng, depth - 1, names))

def simple_expr(rng, names):
    k = rng.random()
    if k < 0.45: return ("v", rng.choice(names))
    if k < 0.6: return ("c", ("v", rng.choice(names)))
    a, b = rng.sample(names, 2)
    return (rng.choice(["u", "i", "d"]), ("v", a), ("v", b))


# Image and preimage statements: (needs_inj, binder over sets, statement, tex, proof). Placeholders: %(A)s %(B)s %(f)s.
IMG2 = [
    (False, "A B", "%(f)s '' %(A)s \\ %(f)s '' %(B)s ⊆ %(f)s '' (%(A)s \\ %(B)s)", "%(f)s(%(A)s) \\setminus %(f)s(%(B)s) \\subseteq %(f)s(%(A)s \\setminus %(B)s)",
     "by\n  rintro y ⟨⟨x, hx, rfl⟩, hy⟩\n  exact ⟨x, ⟨hx, fun hb => hy ⟨x, hb, rfl⟩⟩, rfl⟩", "image"),
    (False, "B", "%(f)s '' (%(f)s ⁻¹' %(B)s) = %(B)s ∩ Set.range %(f)s", "%(f)s(%(f)s^{-1}(%(B)s)) = %(B)s \\cap \\operatorname{range} %(f)s",
     "by\n  ext y\n  constructor\n  · rintro ⟨x, hx, rfl⟩\n    exact ⟨hx, x, rfl⟩\n  · rintro ⟨hy, x, rfl⟩\n    exact ⟨x, hy, rfl⟩", "preimage"),
    (True, "A", "%(f)s ⁻¹' (%(f)s '' %(A)s) = %(A)s", "%(f)s^{-1}(%(f)s(%(A)s)) = %(A)s",
     "by\n  ext x\n  constructor\n  · rintro ⟨y, hy, hxy⟩\n    exact (hf hxy) ▸ hy\n  · intro hx\n    exact ⟨x, hx, rfl⟩", "preimage"),
]
IMG3 = [
    (True, "A B", "%(f)s '' (%(A)s ∩ %(B)s) = %(f)s '' %(A)s ∩ %(f)s '' %(B)s", "%(f)s(%(A)s \\cap %(B)s) = %(f)s(%(A)s) \\cap %(f)s(%(B)s)",
     "by\n  ext y\n  constructor\n  · rintro ⟨x, ⟨ha, hb⟩, rfl⟩\n    exact ⟨⟨x, ha, rfl⟩, ⟨x, hb, rfl⟩⟩\n  · rintro ⟨⟨x, ha, rfl⟩, ⟨x', hb, hx⟩⟩\n    have hxx : x' = x := hf hx\n    subst hxx\n    exact ⟨x', ⟨ha, hb⟩, rfl⟩", "image"),
    (True, "A B", "%(f)s '' (%(A)s \\ %(B)s) = %(f)s '' %(A)s \\ %(f)s '' %(B)s", "%(f)s(%(A)s \\setminus %(B)s) = %(f)s(%(A)s) \\setminus %(f)s(%(B)s)",
     "by\n  ext y\n  constructor\n  · rintro ⟨x, ⟨ha, hb⟩, rfl⟩\n    exact ⟨⟨x, ha, rfl⟩, fun ⟨x', hb', hx⟩ => hb ((hf hx) ▸ hb')⟩\n  · rintro ⟨⟨x, ha, rfl⟩, hy⟩\n    exact ⟨x, ⟨ha, fun hb => hy ⟨x, hb, rfl⟩⟩, rfl⟩", "image"),
    (True, "A B", "%(f)s ⁻¹' (%(f)s '' %(A)s) ∩ %(B)s = %(A)s ∩ %(B)s", "%(f)s^{-1}(%(f)s(%(A)s)) \\cap %(B)s = %(A)s \\cap %(B)s",
     "by\n  ext x\n  constructor\n  · rintro ⟨⟨y, hy, hxy⟩, hb⟩\n    exact ⟨(hf hxy) ▸ hy, hb⟩\n  · rintro ⟨ha, hb⟩\n    exact ⟨⟨x, ha, rfl⟩, hb⟩", "preimage"),
]

def image_statements(rng, difficulty):
    needs_inj, sets, body, tx, proof, _ = rng.choice(IMG2 if difficulty == 2 else IMG3)
    f = rng.choice(["f", "g", "h"]); A, B = rng.sample(["A", "B", "C", "S", "T"], 2)
    sub = {"f": f, "A": A, "B": B}
    names = [{"A": A, "B": B}[c] for c in sets.split()]
    stype = {"A": "α", "B": "β"}
    # sets live in α, except the lone preimage-of-B statement which lives in β
    ssort = "β" if (sets == "B") else "α"
    binder = "{α β : Type*} (%s : α → β) (%s : Set %s)" % (f, " ".join(names), ssort)
    if needs_inj: binder += " (hf : Function.Injective %s)" % f
    stmt = "%s :\n    %s" % (binder, body % sub)
    if sets == "B":  # sets named B in the statement; rename B to the chosen name for the second letter
        pass
    info = "Let \\(%s : \\alpha \\to \\beta\\) be a function%s and let \\(%s\\) be subsets of \\(%s\\). Write \\(%s(X)\\) for the image and \\(%s^{-1}(X)\\) for the preimage of a set \\(X\\). Prove \\[%s.\\]" % (
        f, " that is injective" if needs_inj else "", ", ".join(names), "\\beta" if ssort == "β" else "\\alpha", f, f, tx % sub)
    return info, [Theorem("image_identity", stmt, proof.replace("hf", "hf"), "The stated statement about images and preimages.")]

def set_identities(rng, difficulty):
    if difficulty == 2 or (difficulty == 3 and rng.random() < 0.5):
        return image_statements(rng, difficulty)
    return set_algebra(rng, difficulty)

def set_algebra(rng, difficulty):
    names = rng.sample(["A", "B", "C", "S", "T", "U", "X", "Y", "Z"], 3)
    rows = list(itertools.product([False, True], repeat=3))
    envs = [dict(zip(names, r)) for r in rows]
    hyp = None
    if difficulty < 3:
        while True:
            l, r = rng.choice(LAWS)
            if difficulty == 1:
                m = dict(zip("abc", rng.sample(names, 3)))
                m = {k: ("v", v) for k, v in m.items()}
            else:
                m = {k: simple_expr(rng, names) for k in "abc"}
            e1, e2 = subst(l, m), subst(r, m)
            if lean(e1) == lean(e2) or degenerate(e1) or degenerate(e2): continue
            if difficulty == 2 and size(e1) + size(e2) < 12: continue
            if difficulty == 2 and rng.random() < 0.7 and len(vars_of(e1) | vars_of(e2)) < 3: continue
            break
        if rng.random() < 0.5: e1, e2 = e2, e1
        allowed = envs
    else:
        a, b = rng.sample(names, 2)
        if rng.random() < 0.5:
            hyp = ("sub", a, b, "(h : %s ⊆ %s)" % (a, b), "%s \\subseteq %s" % (a, b), lambda env, a=a, b=b: (not env[a]) or env[b])
        else:
            hyp = ("dis", a, b, "(h : %s ∩ %s = ∅)" % (a, b), "%s \\cap %s = \\emptyset" % (a, b), lambda env, a=a, b=b: not (env[a] and env[b]))
        allowed = [e for e in envs if hyp[5](e)]
        for _ in range(200000):
            e1 = rand_expr(rng, 3, names); e2 = rand_expr(rng, 3, names)
            if lean(e1) == lean(e2) or degenerate(e1) or degenerate(e2) or not (4 <= size(e1) <= 8 and 4 <= size(e2) <= 8): continue
            if len(vars_of(e1) | vars_of(e2)) < 3: continue
            if max(count_vars(e1).values()) > 2 or max(count_vars(e2).values()) > 2: continue
            if not all(ev(e1, e) == ev(e2, e) for e in allowed): continue
            if all(ev(e1, e) == ev(e2, e) for e in envs): continue
            if len({ev(e1, e) for e in allowed}) < 2 or len({ev(e2, e) for e in allowed}) < 2: continue
            break
        else: raise RuntimeError("no identity found")
    assert all(ev(e1, e) == ev(e2, e) for e in allowed)
    binder = "{α : Type*} (%s : Set α)" % " ".join(names) + ((" " + hyp[3]) if hyp else "")
    stmt = "%s :\n    %s = %s" % (binder, lean(e1, True), lean(e2, True))
    if hyp is None:
        proof = "by\n  ext x\n  %s\n  all_goals tauto" % SIMP; extra = ""
    elif hyp[0] == "sub":
        proof = "by\n  ext x\n  have hx : x ∈ %s → x ∈ %s := @h x\n  %s\n  all_goals tauto" % (hyp[1], hyp[2], SIMP)
        extra = " Assume that \\(%s\\)." % hyp[4]
    else:
        proof = ("by\n  ext x\n  have hx : x ∈ %s → x ∈ %s → False := fun ha hb => by\n    have hm : x ∈ %s ∩ %s := ⟨ha, hb⟩\n    simp [h] at hm\n  %s\n  tauto" % (hyp[1], hyp[2], hyp[1], hyp[2], SIMP)).replace("\n  tauto", "\n  all_goals tauto")
        extra = " Assume that \\(%s\\)." % hyp[4]
    info = "Let \\(%s\\) be subsets of a type \\(\\alpha\\).%s Prove the set identity \\[%s = %s.\\]" % (", ".join(names), extra, tex(e1, True), tex(e2, True))
    return info, [Theorem("set_identity", stmt, proof, "The stated identity between sets.")]

# ---------------------------------------------------------------- finset cardinalities
INJ = "have hinj : Function.Injective (fun x : ℕ => %d * x + %d) := by\n    intro x y h\n    simp only at h\n    omega\n  "

def finset_card(rng, difficulty):
    a = rng.randrange(2, 10); b = rng.randrange(0, 10)
    f = "(fun x : ℕ => %d * x + %d)" % (a, b); ftex = "x \\mapsto %dx + %d" % (a, b)
    inj = INJ % (a, b)
    if difficulty == 1:
        if rng.random() < 0.5:
            stmt = "(s : Finset ℕ) :\n    (s.image %s).card = s.card" % f
            proof = "by\n  " + inj + "exact Finset.card_image_of_injective s hinj"
            info = "Let \\(f(x) = %dx + %d\\) on the natural numbers and let \\(s\\) be a finite set of natural numbers. Prove that the image \\(f(s)\\) has the same number of elements as \\(s\\)." % (a, b)
        else:
            stmt = "(s t : Finset ℕ) :\n    ((s.image %s) ×ˢ t).card = s.card * t.card" % f
            proof = "by\n  " + inj + "rw [Finset.card_product, Finset.card_image_of_injective s hinj]"
            info = "Let \\(f(x) = %dx + %d\\) on the natural numbers and let \\(s, t\\) be finite sets of natural numbers. Prove that the product \\(f(s) \\times t\\) has \\(|s| \\cdot |t|\\) elements." % (a, b)
        return info, [Theorem("card_fact", stmt, proof, "A cardinality fact about finite sets.")]
    if difficulty == 2:
        if rng.random() < 0.5:
            stmt = "(s t : Finset ℕ) :\n    ((s ∪ t).image %s).card + ((s ∩ t).image %s).card = s.card + t.card" % (f, f)
            proof = ("by\n  " + inj + "rw [Finset.image_union, Finset.image_inter _ _ hinj, Finset.card_union_add_card_inter,\n    Finset.card_image_of_injective s hinj, Finset.card_image_of_injective t hinj]")
            info = "Let \\(f(x) = %dx + %d\\) on the natural numbers and let \\(s, t\\) be finite sets of natural numbers. Prove that \\[|f(s \\cup t)| + |f(s \\cap t)| = |s| + |t|.\\]" % (a, b)
        else:
            stmt = "(s t : Finset ℕ) :\n    ((s \\ t).image %s).card + (s ∩ t).card = s.card" % f
            proof = ("by\n  " + inj + "rw [Finset.card_image_of_injective _ hinj]\n  have h := Finset.card_sdiff_add_card_inter s t\n  omega")
            info = "Let \\(f(x) = %dx + %d\\) on the natural numbers and let \\(s, t\\) be finite sets of natural numbers. Prove that \\[|f(s \\setminus t)| + |s \\cap t| = |s|.\\]" % (a, b)
        return info, [Theorem("card_fact", stmt, proof, "A cardinality fact about finite sets.")]
    if rng.random() < 0.5:
        stmt = "(s t : Finset ℕ) (h : Disjoint s t) :\n    ((s ∪ t).image %s).card = s.card + t.card" % f
        proof = "by\n  " + inj + "rw [Finset.card_image_of_injective _ hinj, Finset.card_union_of_disjoint h]"
        info = "Let \\(f(x) = %dx + %d\\) on the natural numbers and let \\(s, t\\) be disjoint finite sets of natural numbers. Prove that \\(|f(s \\cup t)| = |s| + |t|\\)." % (a, b)
        return info, [Theorem("card_fact", stmt, proof, "A cardinality fact about finite sets.")]
    lemma = Theorem("incl_excl", "(s t u : Finset ℕ) :\n    (s ∪ t ∪ u).card + (s ∩ t).card + (s ∩ u).card + (t ∩ u).card = s.card + t.card + u.card + (s ∩ t ∩ u).card",
        "by\n  have h1 := Finset.card_union_add_card_inter (s ∪ t) u\n  have h2 := Finset.card_union_add_card_inter s t\n  have h3 := Finset.card_union_add_card_inter (s ∩ u) (t ∩ u)\n"
        "  have e1 : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u := Finset.union_inter_distrib_right s t u\n  have e2 : s ∩ u ∩ (t ∩ u) = s ∩ t ∩ u := by\n    ext x\n    simp only [Finset.mem_inter]\n    tauto\n  rw [e1] at h1\n  rw [e2] at h3\n  omega",
        "Inclusion and exclusion for three finite sets.")
    main = Theorem("card_union_three", "(s t u : Finset ℕ) :\n    (s ∪ t ∪ u).card = s.card + t.card + u.card - (s ∩ t).card - (s ∩ u).card - (t ∩ u).card + (s ∩ t ∩ u).card",
        "by\n  have h := incl_excl s t u\n  have h7 : (s ∩ t ∩ u).card ≤ (s ∪ t ∪ u).card :=\n    Finset.card_le_card (fun x hx => by\n      simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢\n      tauto)\n  omega",
        "The size of a union of three finite sets, in terms of the sizes of the intersections.", weight=2.0)
    info = ("Let \\(s, t, u\\) be finite sets of natural numbers. First prove the identity \\[|s \\cup t \\cup u| + |s \\cap t| + |s \\cap u| + |t \\cap u| = |s| + |t| + |u| + |s \\cap t \\cap u|.\\] "
            "Then use it to prove the following, where subtraction is truncated subtraction on the natural numbers: \\[|s \\cup t \\cup u| = |s| + |t| + |u| - |s \\cap t| - |s \\cap u| - |t \\cap u| + |s \\cap t \\cap u|.\\]")
    return info, [lemma, main]

# ---------------------------------------------------------------- relations
def relations(rng, difficulty):
    if difficulty == 1:
        m = rng.randrange(2, 13)
        if rng.random() < 0.5:
            rel = "fun x y : ℤ => %d ∣ x - y" % m; tx = "x \\sim y \\iff %d \\mid x - y" % m
        else:
            rel = "fun x y : ℤ => x %% %d = y %% %d" % (m, m); tx = "x \\sim y \\iff x \\bmod %d = y \\bmod %d" % (m, m)
        proof = "⟨fun x => by omega, fun {x y} h => by omega, fun {x y z} h1 h2 => by omega⟩"
        info = "On the integers define \\(%s\\). Prove that \\(\\sim\\) is an equivalence relation." % tx
        return info, [Theorem("rel_equiv", ":\n    Equivalence (%s)" % rel, proof, "The relation is reflexive, symmetric and transitive.")]
    if difficulty == 2:
        if rng.random() < 0.5:
            a = rng.randrange(2, 8)
            rel = "fun p q : ℕ × ℕ => p.1 + %d * q.2 = q.1 + %d * p.2" % (a, a)
            tx = "(x_1, y_1) \\sim (x_2, y_2) \\iff x_1 + %d y_2 = x_2 + %d y_1" % (a, a)
            proof = "⟨fun p => by omega, fun {p q} h => by omega, fun {p q r} h1 h2 => by omega⟩"
            info = "On pairs of natural numbers define \\(%s\\). Prove that \\(\\sim\\) is an equivalence relation." % tx
        else:
            m = rng.randrange(2, 13); k = rng.choice([2, 3, 4])
            rel = "fun x y : ℤ => %d ∣ x ^ %d - y ^ %d" % (m, k, k)
            tx = "x \\sim y \\iff %d \\mid x^{%d} - y^{%d}" % (m, k, k)
            proof = ("⟨fun x => by simp, fun {x y} h => (dvd_sub_comm).mp h, fun {x y z} h1 h2 => by\n    have h := dvd_add h1 h2\n    rwa [sub_add_sub_cancel] at h⟩")
            info = "On the integers define \\(%s\\). Prove that \\(\\sim\\) is an equivalence relation." % tx
        return info, [Theorem("rel_equiv", ":\n    Equivalence (%s)" % rel, proof, "The relation is reflexive, symmetric and transitive.")]
    n = rng.choice(["m", "n", "q"])
    form = rng.choice(["dvd", "modeq"]); second = rng.choice(["mul", "pow"])
    if form == "dvd":
        rel = "fun x y : ℤ => %s ∣ x - y" % n; tx = "x \\sim y \\iff %s \\mid x - y" % n
        p1 = ("⟨fun x => by simp, fun {x y} h => (dvd_sub_comm).mp h, fun {x y z} h1 h2 => by\n    have h := dvd_add h1 h2\n    rwa [sub_add_sub_cancel] at h⟩")
        hyp = lambda a, b: "%s ∣ %s - %s" % (n, a, b)
        add_p = "by\n  have h := dvd_add h1 h2\n  have e : (a + c) - (b + d) = (a - b) + (c - d) := by ring\n  rw [e]\n  exact h"
        base = lambda lhs, rhs: "%s ∣ %s - %s" % (n, ("(%s)" % lhs) if "+" in lhs else lhs, ("(%s)" % rhs) if "+" in rhs else rhs)
        tex_h = lambda a, b: "%s \\mid %s - %s" % (n, ("(%s)" % a) if "+" in a else a, ("(%s)" % b) if "+" in b else b)
    else:
        rel = "fun x y : ℤ => x ≡ y [ZMOD %s]" % n; tx = "x \\sim y \\iff x \\equiv y \\pmod{%s}" % n
        p1 = "Int.ModEq.refl, fun {x y} h => h.symm, fun {x y z} h1 h2 => h1.trans h2"
        p1 = "⟨%s⟩" % p1.replace("Int.ModEq.refl,", "fun x => Int.ModEq.refl x,")
        hyp = lambda a, b: "%s ≡ %s [ZMOD %s]" % (a, b, n)
        add_p = "h1.add h2"
        base = lambda lhs, rhs: "%s ≡ %s [ZMOD %s]" % (lhs, rhs, n)
        tex_h = lambda a, b: "%s \\equiv %s \\pmod{%s}" % (a, b, n)
    t1 = Theorem("rel_equiv", "(%s : ℤ) :\n    Equivalence (%s)" % (n, rel), p1, "The relation is reflexive, symmetric and transitive.")
    t2 = Theorem("rel_add", "(%s a b c d : ℤ) (h1 : %s) (h2 : %s) :\n    %s" % (n, hyp("a", "b"), hyp("c", "d"), base("a + c", "b + d")), add_p, "The relation is compatible with addition.")
    if second == "mul":
        if form == "dvd":
            pm = "by\n  have e : a * c - b * d = a * (c - d) + (a - b) * d := by ring\n  rw [e]\n  exact dvd_add (dvd_mul_of_dvd_right h2 a) (dvd_mul_of_dvd_left h1 d)"
        else: pm = "h1.mul h2"
        t3 = Theorem("rel_mul", "(%s a b c d : ℤ) (h1 : %s) (h2 : %s) :\n    %s" % (n, hyp("a", "b"), hyp("c", "d"), base("a * c", "b * d")), pm, "The relation is compatible with multiplication.", weight=2.0)
        what = "\\(a c \\sim b d\\)"; tx3 = "multiplication: if \\(%s\\) and \\(%s\\) then \\(%s\\)" % (tex_h("a", "b"), tex_h("c", "d"), tex_h("ac", "bd"))
    else:
        if form == "dvd":
            pm = "by\n  exact h.trans (sub_dvd_pow_sub_pow a b k)"
        else: pm = "h.pow k"
        t3 = Theorem("rel_pow", "(%s a b : ℤ) (k : ℕ) (h : %s) :\n    %s" % (n, hyp("a", "b"), base("a ^ k", "b ^ k")), pm, "The relation is compatible with taking powers.", weight=2.0)
        tx3 = "powers: if \\(%s\\) then \\(%s\\) for every natural number \\(k\\)" % (tex_h("a", "b"), tex_h("a^k", "b^k"))
    info = ("For an integer \\(%s\\), define a relation on the integers by \\(%s\\). Prove three things: (1) \\(\\sim\\) is an equivalence relation; (2) \\(\\sim\\) is compatible with addition: if \\(%s\\) and \\(%s\\) then \\(%s\\); (3) \\(\\sim\\) is compatible with %s."
            % (n, tx, tex_h("a", "b"), tex_h("c", "d"), tex_h("a+c", "b+d"), tx3))
    return info, [t1, t2, t3]

def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    info, thms = {"quantifiers": quantifiers, "set_identities": set_identities, "finset_card": finset_card, "relations": relations}[family](rng, difficulty)
    titles = {"quantifiers": "Prove a statement of predicate logic", "set_identities": "Prove an identity between sets",
              "finset_card": "Prove a cardinality fact about finite sets", "relations": "Prove properties of a relation"}
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="prove", title=titles[family],
        informal="Prove the following.\n\n" + info, theorems=thms)
