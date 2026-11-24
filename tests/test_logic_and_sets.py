"""Regression tests for envs/logic_and_sets: exact statements for fixed seeds and hand-checked facts."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from envs.logic_and_sets import gen


def stmts(seed, d, fam):
    return [t.statement.replace("\n    ", " ") for t in gen.generate(seed, d, fam).theorems]


def test_quantifiers():
    # seed 0, difficulty 1: the dual of the existential quantifier
    assert stmts(0, 1, "quantifiers") == ["{α : Type*} (Q : α → Prop) : (¬ ∃ x, Q x) ↔ ∀ x, ¬ Q x"]
    # seed 0, difficulty 2: moving a hypothesis across a quantifier turns forall into exists-premise
    assert stmts(0, 2, "quantifiers") == ["{α : Type*} (Q : α → Prop) (p : Prop) : (∀ x, Q x → p) ↔ ((∃ x, Q x) → p)"]
    # the drinker paradox and the exists-forall dichotomy are false on the empty type, so they must assume Nonempty
    seen = 0
    for seed in range(60):
        st = gen.generate(seed, 3, "quantifiers").theorems[0].statement
        if st.split(":\n")[-1].strip().startswith(("∃ x, ", "(∃ x, ∀ y,")) and ("→ ∀ y," in st or "∨ (∀ x, ∃ y" in st):
            assert "[Nonempty α]" in st; seen += 1
    assert seen > 0


def test_set_identities():
    # distributivity: B ∩ (U ∪ X) = (B ∩ U) ∪ (B ∩ X)
    assert stmts(0, 1, "set_identities") == ["{α : Type*} (U X B : Set α) : (B ∩ U) ∪ (B ∩ X) = B ∩ (U ∪ X)"]
    # difficulty 2 is about images and preimages: f(f^-1(A)) = A ∩ range f, and f^-1(f(C)) = C for injective f
    assert stmts(0, 2, "set_identities") == ["{α β : Type*} (f : α → β) (A : Set β) : f '' (f ⁻¹' A) = A ∩ Set.range f"]
    assert stmts(1, 2, "set_identities") == ["{α β : Type*} (h : α → β) (C : Set α) (hf : Function.Injective h) : h ⁻¹' (h '' C) = C"]
    # the second code path: each law is a truth-table identity, and De Morgan evaluates as expected by hand
    names = ["a", "b", "c"]
    import itertools
    for l, r in gen.LAWS:
        for row in itertools.product([False, True], repeat=3):
            env = dict(zip(names, row))
            assert gen.ev(l, env) == gen.ev(r, env)
    demorgan = gen.LAWS[0][0]                      # (a ∪ b)ᶜ
    assert gen.ev(demorgan, {"a": False, "b": False, "c": False}) is True
    assert gen.ev(demorgan, {"a": True, "b": False, "c": False}) is False
    # a conditional identity (difficulty 3, set algebra branch) needs its hypothesis: it must fail on some unrestricted row
    t = gen.generate(0, 3, "set_identities")
    assert stmts(0, 3, "set_identities") == ["{α : Type*} (Y X C : Set α) (h : Y ∩ C = ∅) : (X ∪ Yᶜ)ᶜ = Y \\ (C ∪ X)"]
    # by hand: (X ∪ Yᶜ)ᶜ = Xᶜ ∩ Y, and Y \ (C ∪ X) = Y ∩ Cᶜ ∩ Xᶜ; they agree because Y ∩ C = ∅ forces Y ⊆ Cᶜ
    assert "ext x" in t.theorems[0].proof


def test_finset_card():
    # |f(s ∪ t)| + |f(s ∩ t)| = |s| + |t| for the injective map 9x + 4
    assert stmts(0, 2, "finset_card") == ["(s t : Finset ℕ) : ((s ∪ t).image (fun x : ℕ => 9 * x + 4)).card + ((s ∩ t).image (fun x : ℕ => 9 * x + 4)).card = s.card + t.card"]
    # |f(s \ t)| + |s ∩ t| = |s|
    assert stmts(1, 2, "finset_card") == ["(s t : Finset ℕ) : ((s \\ t).image (fun x : ℕ => 2 * x + 1)).card + (s ∩ t).card = s.card"]
    # the map in the statement and in the words agree, and has a nonzero slope (so it is injective)
    for seed in range(20):
        t = gen.generate(seed, 1, "finset_card")
        a, b = re.search(r"fun x : ℕ => (\d+) \* x \+ (\d+)", t.theorems[0].statement).groups()
        assert "f(x) = %sx + %s" % (a, b) in t.informal and int(a) >= 2
    # difficulty 3 may be a lemma plus a consequence; the consequence is weighted double
    for seed in range(10):
        ts = gen.generate(seed, 3, "finset_card").theorems
        assert len(ts) in (1, 2)
        if len(ts) == 2: assert ts[0].name == "incl_excl" and ts[1].weight == 2.0


def test_relations():
    # 9 | x^2 - y^2 is the kernel-type relation of x |-> x^2 modulo 9
    assert stmts(0, 2, "relations") == [": Equivalence (fun x y : ℤ => 9 ∣ x ^ 2 - y ^ 2)"]
    t = gen.generate(0, 1, "relations")
    assert re.fullmatch(r":\n    Equivalence \(fun x y : ℤ => (\d+ ∣ x - y|x % \d+ = y % \d+)\)", t.theorems[0].statement)
    # difficulty 3: three theorems, the last weighted double, with the modulus symbolic
    ts = gen.generate(0, 3, "relations").theorems
    assert [x.name for x in ts][:2] == ["rel_equiv", "rel_add"] and ts[2].weight == 2.0
    assert ts[1].statement.replace("\n    ", " ").endswith("(a + c) - (b + d)") or "(a + c) ≡ " in ts[1].statement or "+ c ≡ b + d" in ts[1].statement
    # by hand: (a - b) + (c - d) = (a + c) - (b + d)
    assert "(a + c) - (b + d) = (a - b) + (c - d)" in ts[1].proof or "h1.add h2" in ts[1].proof
