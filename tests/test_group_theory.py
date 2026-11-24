"""Regression tests for envs/group_theory/gen.py (plain asserts)."""
import re
from envs.group_theory.gen import generate, FAMILIES

def stmts(t): return [x.statement.replace("\n", " ") for x in t.theorems]
def squash(s): return re.sub(r"\s+", " ", s)

# involution: exact statements for fixed seeds, derived by hand from the hypothesis lists
t = generate(0, 1, "involution")
assert squash(stmts(t)[0]) == "{G : Type*} [Group G] (h : ∀ g : G, g⁻¹ = g) : ∀ x y : G, x * y = y * x", stmts(t)
t = generate(3, 3, "involution")
assert [x.name for x in t.theorems] == ["involution_comm", "power_of_product"]
assert "(u * v) ^ 2 = u ^ 2 * v ^ 2" in stmts(t)[0] and "∀ u v : A, u * v = v * u" in stmts(t)[0]
tail = squash(stmts(t)[1]).split(") : ")[-1]
n = int(re.match(r"\(u \* v\) \^ (\d+) = u", tail).group(1)); assert 3 <= n <= 9 and tail == "(u * v) ^ %d = u ^ %d * v ^ %d" % (n, n, n)
assert abs(sum(x.weight for x in t.theorems) - 1.0) < 1e-9

# inverse: a three-term rotation, and the right-inverse lemma pair
t = generate(1, 3, "inverse")
assert squash(stmts(t)[0]) == "{A : Type*} [Group A] (x₁ x₂ x₃ x₄ x₅ x₆ : A) (h : x₁ * x₂ * x₃ * x₄ * x₅ * x₆ = 1) : x₆ * x₁ * x₂ * x₃ * x₄ * x₅ = 1", stmts(t)
t = generate(0, 3, "inverse")
assert [x.name for x in t.theorems] == ["right_inverse_comm", "inverse_unique"]
assert "∀ g k : S, g * k = 1 → k * g = 1" in squash(stmts(t)[0]) and "∃ k, g * k = 1" in stmts(t)[0]
for s in range(10):                      # rotation: same factors on both sides, one rotated
    t = generate(s, 1, "inverse")
    st = squash(stmts(t)[0])
    if "rotate" in t.theorems[0].name:
        facs = re.findall(r"\(([^()]*) : \w+\)", st)[0].split()
        lhs = re.search(r"\(h : (.*) = 1\)", st).group(1).split(" * "); rhs = st.split(": ")[-1].replace(" = 1", "").split(" * ")
        assert lhs == facs and sorted(rhs) == sorted(facs) and rhs != lhs

# subgroup: Lagrange numbers (index times order is the group order) and the union theorem
t = generate(3, 2, "subgroup")
assert squash(stmts(t)[0]) == "{G : Type*} [Group G] (hG : Nat.card G = 45) (L : Subgroup G) (hH : Nat.card L = 9) : L.index = 5", stmts(t)
assert 45 == 9 * 5
for s in range(40):
    t = generate(s, 2, "subgroup")
    if t.theorems[0].name == "subgroup_index":
        a, b, c = map(int, re.findall(r"= (\d+)", stmts(t)[0])); assert a == b * c, (a, b, c)
t = generate(0, 3, "subgroup")
assert t.theorems[0].name == "subgroup_union" and stmts(t)[0].endswith(": A ≤ B ∨ B ≤ A")
for s in range(40):
    t = generate(s, 3, "subgroup")
    if t.theorems[0].name == "pow_card":
        p = int(re.search(r"= (\d+)", stmts(t)[0]).group(1)); assert p in (3, 5, 7, 11, 13, 17, 19) and all(p % d for d in range(2, p))

# hom: exact statements
t = generate(0, 1, "hom")
assert squash(stmts(t)[0]) == "{X Y : Type*} [Group X] [Group Y] (f : X →* Y) (x y : X) : f x = f y ↔ x⁻¹ * y ∈ f.ker", stmts(t)
t = generate(1, 1, "hom")
assert squash(stmts(t)[0]) == "{A B : Type*} [Group A] [Group B] (f : A →* B) {x y : A} (hx : x ∈ f.ker) (hy : y ∈ f.ker) : x * y⁻¹ ∈ f.ker", stmts(t)
t = generate(1, 2, "hom")
assert squash(stmts(t)[0]) == "{G K : Type*} [Group G] [Group K] (f : G →* K) (h : ∀ g : G, f g = 1 → g = 1) : Function.Injective f", stmts(t)
t = generate(0, 2, "hom")
assert squash(stmts(t)[0]) == "{G H Z : Type*} [Group G] [Group H] [Group Z] (f : G →* H) (g : H →* Z) : f.ker ≤ (g.comp f).ker", stmts(t)
for s in range(30):                       # the three type names of a composition task are distinct
    t = generate(s, 2, "hom"); names = re.match(r"\{([^:]*) : Type\*\}", squash(stmts(t)[0])).group(1).split()
    assert len(names) == len(set(names)), names
for s in range(30):
    t = generate(s, 3, "hom")
    if t.theorems[-1].name == "ker_comp_eq": assert abs(sum(x.weight for x in t.theorems) - 1.0) < 1e-9

# general: determinism, defaults, kinds
for f in FAMILIES:
    for d in (1, 2, 3):
        a, b = generate(5, d, f), generate(5, d, f)
        assert a.reference_solution() == b.reference_solution() and a.kind == "prove" and a.family == f
assert generate(0, 1).family == sorted(FAMILIES)[0] and generate(3, 1).family == sorted(FAMILIES)[3]
print("test_group_theory ok")
