"""Definitions from words: write `f : ℕ → ℕ` from an English description.

Two code paths: the Lean reference definition and the expected values are produced separately.
The expected values in the hidden test come from the Python functions below; the Lean reference
is compiled and run against them in the self-test. Elementary number theory only (MSC 11A, 11B).
"""
from math import gcd, isqrt
from arena.core import Task, Theorem, rng_for

ENV = "definitions"
FAMILIES = ["count", "divisors", "extremum", "pairs", "sequence", "sum"]

def digits(k): return [int(c) for c in str(k)] if k > 0 else []
def is_prime(k): return k >= 2 and all(k % d for d in range(2, isqrt(k) + 1))
def is_square(k): return isqrt(k) ** 2 == k
def squarefree(k): return k >= 1 and all(k % (d * d) for d in range(2, isqrt(k) + 1))
def ndiv(k): return sum(1 for d in range(1, k + 1) if k % d == 0)

# A predicate on a positive integer k: (words, lean, python, period or None)
def pred(rng, var, allow_n=False, periodic=False):
    lv = var; var = "\\(%s\\)" % var   # `var` for words, `lv` for Lean
    kinds = ["div", "mod", "coprime_c"] + ([] if periodic else ["prime", "square", "digitsum", "palin", "squarefree"]) + (["coprime_n", "divides_n"] if allow_n else [])
    kind = rng.choice(kinds)
    if kind == "div":
        d = rng.choice([2, 3, 4, 5, 6, 7])
        return ("%s is divisible by %d" % (var, d), "%d ∣ %s" % (d, lv), lambda k, n, d=d: k % d == 0, d)
    if kind == "mod":
        m = rng.choice([3, 4, 5, 6, 7, 8, 9]); r = rng.randrange(1, m)
        return ("%s leaves remainder %d on division by %d" % (var, r, m), "%s %% %d = %d" % (lv, m, r), lambda k, n, m=m, r=r: k % m == r, m)
    if kind == "coprime_c":
        c = rng.choice([6, 10, 12, 14, 15, 21, 30])
        return ("%s is coprime to %d" % (var, c), "Nat.Coprime %s %d" % (lv, c), lambda k, n, c=c: gcd(k, c) == 1, c)
    if kind == "prime":
        return ("%s is prime" % var, "Nat.Prime %s" % lv, lambda k, n: is_prime(k), None)
    if kind == "square":
        return ("%s is a perfect square" % var, "IsSquare %s" % lv, lambda k, n: is_square(k), None)
    if kind == "squarefree":
        return ("%s is squarefree (no square larger than 1 divides it)" % var, "Squarefree %s" % lv, lambda k, n: squarefree(k), None)
    if kind == "digitsum":
        m = rng.choice([3, 4, 5, 7]); r = rng.randrange(0, m)
        return ("the sum of the decimal digits of %s leaves remainder %d on division by %d" % (var, r, m),
                "(Nat.digits 10 %s).sum %% %d = %d" % (lv, m, r), lambda k, n, m=m, r=r: sum(digits(k)) % m == r, None)
    if kind == "palin":
        return ("the decimal digits of %s read the same forwards and backwards" % var,
                "Nat.digits 10 %s = (Nat.digits 10 %s).reverse" % (lv, lv), lambda k, n: str(k) == str(k)[::-1], None)
    if kind == "coprime_n":
        return ("%s is coprime to \\(n\\)" % var, "Nat.Coprime %s n" % lv, lambda k, n: gcd(k, n) == 1, None)
    return ("%s divides \\(n\\)" % var, "%s ∣ n" % lv, lambda k, n: n % k == 0, None)

def combine(rng, difficulty, var, allow_n=False, periodic=False):
    """One predicate at difficulty 1, two joined by and / or / and-not above that."""
    a = pred(rng, var, allow_n, periodic)
    if difficulty == 1: return a
    while True:
        b = pred(rng, var, allow_n, periodic)
        if b[1].split()[0:2] != a[1].split()[0:2] and b[1] != a[1]: break
    op = rng.choice(["and", "or", "andnot"])
    per = (a[3] * b[3] // gcd(a[3], b[3])) if a[3] and b[3] else None
    if op == "and": return ("%s and %s" % (a[0], b[0]), "(%s) ∧ (%s)" % (a[1], b[1]), lambda k, n: a[2](k, n) and b[2](k, n), per)
    if op == "or": return ("%s or %s (or both)" % (a[0], b[0]), "(%s) ∨ (%s)" % (a[1], b[1]), lambda k, n: a[2](k, n) or b[2](k, n), per)
    return ("%s but it is not the case that %s" % (a[0], b[0]), "(%s) ∧ ¬ (%s)" % (a[1], b[1]), lambda k, n: a[2](k, n) and not b[2](k, n), per)

def weight(rng, var):
    return rng.choice([
        ("\\(%s\\)" % var, "%s" % var, lambda k: k),
        ("\\(%s^2\\)" % var, "%s ^ 2" % var, lambda k: k * k),
        ("the digit sums \\(s(%s)\\), where \\(s(m)\\) is the sum of the decimal digits of \\(m\\)," % var, "(Nat.digits 10 %s).sum" % var, lambda k: sum(digits(k))),
        ("the values \\(\\tau(%s)\\), where \\(\\tau(m)\\) is the number of positive divisors of \\(m\\)," % var, "(Nat.divisors %s).card" % var, lambda k: ndiv(k)),
    ])

def build(rng, family, difficulty):
    """Returns (description, lean body with `n` free or a full equation-style definition, python f, N)."""
    N = 40
    if family == "count":
        w, l, p, _ = combine(rng, difficulty, "k", allow_n=difficulty == 3)
        desc = "\\(f(n)\\) is the number of integers \\(k\\) with \\(1 \\le k \\le n\\) such that %s." % w
        return desc, "((Finset.Icc 1 n).filter (fun k => %s)).card" % l, lambda n: sum(1 for k in range(1, n + 1) if p(k, n)), N
    if family == "sum":
        w, l, p, _ = combine(rng, max(1, difficulty - 1), "k", allow_n=difficulty == 3)
        gw, gl, g = weight(rng, "k") if difficulty > 1 else ("\\(k\\)", "k", lambda k: k)
        desc = "\\(f(n)\\) is the sum of %s over all integers \\(k\\) with \\(1 \\le k \\le n\\) such that %s. An empty sum is 0." % (gw, w)
        return desc, "∑ k ∈ (Finset.Icc 1 n).filter (fun k => %s), %s" % (l, gl), lambda n: sum(g(k) for k in range(1, n + 1) if p(k, n)), N
    if family == "divisors":
        w, l, p, _ = combine(rng, max(1, difficulty - 1), "d")
        if difficulty == 1:
            desc = "\\(f(n)\\) is the number of positive divisors \\(d\\) of \\(n\\) such that %s. Take \\(f(0) = 0\\)." % w
            return desc, "((Nat.divisors n).filter (fun d => %s)).card" % l, lambda n: sum(1 for d in range(1, n + 1) if n % d == 0 and p(d, n)), N
        gw, gl, g = weight(rng, "d")
        desc = "\\(f(n)\\) is the sum of %s over all positive divisors \\(d\\) of \\(n\\) such that %s. An empty sum is 0, and \\(f(0) = 0\\)." % (gw, w)
        return desc, "∑ d ∈ (Nat.divisors n).filter (fun d => %s), %s" % (l, gl), lambda n: sum(g(d) for d in range(1, n + 1) if n % d == 0 and p(d, n)), N
    if family == "extremum":
        if rng.random() < 0.5:
            w, l, p, _ = combine(rng, difficulty, "k")
            desc = "\\(f(n)\\) is the largest integer \\(k\\) with \\(1 \\le k \\le n\\) such that %s. If there is no such \\(k\\), then \\(f(n) = 0\\)." % w
            return desc, "((List.range (n + 1)).filter (fun k => decide (1 ≤ k ∧ (%s)))).foldl max 0" % l, lambda n: max([k for k in range(1, n + 1) if p(k, n)] or [0]), N
        w, l, p, per = combine(rng, min(difficulty, 2), "k", periodic=True)
        while not any(p(k, 0) for k in range(1, per + 1)):
            w, l, p, per = combine(rng, min(difficulty, 2), "k", periodic=True)
        strict = difficulty == 3 or rng.random() < 0.5
        desc = "\\(f(n)\\) is the smallest integer \\(k\\) with \\(k %s n\\) and \\(k \\ge 1\\) such that %s." % (">" if strict else "\\ge", w)
        start = "n + 1" if strict else "max n 1"
        def py(n, p=p, strict=strict):
            k = n + 1 if strict else max(n, 1)
            while not p(k, n): k += 1
            return k
        return desc, "(((List.range %d).map (fun i => %s + i)).find? (fun k => decide (%s))).getD 0" % (per + 1, start, l), py, N
    if family == "pairs":
        N = 25
        rels = [
            ("\\(\\gcd(a, b) = %d\\)", "Nat.gcd p.1 p.2 = %d", lambda a, b, n, c: gcd(a, b) == c, [1, 2, 3]),
            ("\\(a \\cdot b \\le n\\)", "p.1 * p.2 ≤ n", lambda a, b, n, c: a * b <= n, [0]),
            ("\\(a\\) divides \\(b\\)", "p.1 ∣ p.2", lambda a, b, n, c: b % a == 0, [0]),
            ("\\(a^2 + b^2 \\le n^2\\)", "p.1 ^ 2 + p.2 ^ 2 ≤ n ^ 2", lambda a, b, n, c: a * a + b * b <= n * n, [0]),
            ("\\(a + b\\) is prime", "Nat.Prime (p.1 + p.2)", lambda a, b, n, c: is_prime(a + b), [0]),
            ("\\(a \\cdot b\\) is a perfect square", "IsSquare (p.1 * p.2)", lambda a, b, n, c: is_square(a * b), [0]),
            ("\\(a + b\\) is divisible by %d", "%d ∣ p.1 + p.2", lambda a, b, n, c: (a + b) % c == 0, [3, 4, 5]),
            ("\\(a \\cdot b = n\\)", "p.1 * p.2 = n", lambda a, b, n, c: a * b == n, [0]),
        ]
        def pick():
            w, l, r, cs = rng.choice(rels); c = rng.choice(cs)
            return (w % c if "%d" in w else w), (l % c if "%d" in l else l), (lambda a, b, n, r=r, c=c: r(a, b, n, c))
        w, l, r = pick()
        order = ""
        if difficulty >= 2:
            order_kind = rng.choice(["le", "lt"])
            order = " and \\(a %s b\\)" % ("\\le" if order_kind == "le" else "<")
            l = "(%s) ∧ p.1 %s p.2" % (l, "≤" if order_kind == "le" else "<")
            r0 = r; r = (lambda a, b, n, r0=r0, k=order_kind: r0(a, b, n) and (a <= b if k == "le" else a < b))
        if difficulty == 3:
            w2, l2, r2 = pick()
            while w2 == w: w2, l2, r2 = pick()
            w = w + ", " + w2; l = "(%s) ∧ (%s)" % (l, l2); r1 = r; r = (lambda a, b, n, r1=r1, r2=r2: r1(a, b, n) and r2(a, b, n))
        desc = "\\(f(n)\\) is the number of ordered pairs \\((a, b)\\) of integers with \\(1 \\le a \\le n\\) and \\(1 \\le b \\le n\\) such that %s%s." % (w, order)
        return desc, "((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => %s)).card" % l, lambda n: sum(1 for a in range(1, n + 1) for b in range(1, n + 1) if r(a, b, n)), N
    # sequence
    N = 28
    m = rng.choice([7, 10, 11, 13, 17, 100, 101]); c0, c1 = rng.randrange(0, 5), rng.randrange(1, 6)
    p, q = rng.randrange(1, 5), rng.randrange(1, 5); r = rng.randrange(0, 4) if difficulty >= 2 else 0
    rec = "%s\\,a(n+1) + %s\\,a(n)%s" % (p if p > 1 else "", q if q > 1 else "", (" + %d" % r) if r else "")
    lean_rec = "(%d * a (n + 1) + %d * a n + %d) %% %d" % (p, q, r, m)
    seqdesc = "Let \\(a(0) = %d\\), \\(a(1) = %d\\) and, for \\(n \\ge 0\\), let \\(a(n+2)\\) be the remainder of \\(%s\\) on division by %d." % (c0, c1, rec, m)
    def a(n, memo={}):
        key = (c0, c1, p, q, r, m)
        vals = memo.setdefault(key, [c0, c1])
        while len(vals) <= n: vals.append((p * vals[-1] + q * vals[-2] + r) % m)
        return vals[n]
    helper = "def a : ℕ → ℕ\n  | 0 => %d\n  | 1 => %d\n  | n + 2 => %s\n" % (c0, c1, lean_rec)
    if difficulty == 1:
        return seqdesc + " Then \\(f(n) = a(n)\\).", ("FULL", "def f : ℕ → ℕ\n  | 0 => %d\n  | 1 => %d\n  | n + 2 => (%d * f (n + 1) + %d * f n + %d) %% %d\n" % (c0, c1, p, q, r, m)), a, N
    if difficulty == 2:
        return seqdesc + " Then \\(f(n) = a(0) + a(1) + \\dots + a(n)\\).", ("FULL", helper + "\ndef f (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), a i\n"), lambda n: sum(a(i) for i in range(n + 1)), N
    return (seqdesc + " Then \\(f(n)\\) is the number of indices \\(i\\) with \\(0 \\le i < n\\) such that \\(a(i) < a(i+1)\\).",
            ("FULL", helper + "\ndef f (n : ℕ) : ℕ := ((Finset.range n).filter (fun i => a i < a (i + 1))).card\n"), lambda n: sum(1 for i in range(n) if a(i) < a(i + 1)), N)

def generate(seed, difficulty, family=None):
    family = family or sorted(FAMILIES)[seed % len(FAMILIES)]
    rng = rng_for(ENV + "/" + family, seed, difficulty)
    while True:
        desc, lean, py, N = build(rng, family, difficulty)
        vals = [py(n) for n in range(N)]
        if len(set(vals)) >= 6: break          # reject near-constant functions
    solution = lean[1] if isinstance(lean, tuple) else "def f (n : ℕ) : ℕ := %s\n" % lean
    shown = [n for n in (3, 10, 17, 24) if n < N]
    examples = "\n".join("- \\(f(%d) = %d\\)" % (n, vals[n]) for n in shown)
    test = Theorem("hidden_values", ": (List.range %d).map f = [%s]" % (N, ", ".join(map(str, vals))), "by native_decide")
    return Task(env=ENV, family=family, seed=seed, difficulty=difficulty, kind="define",
        title="Define a function from its description",
        informal="Define the function \\(f\\) from the natural numbers (including 0) to the natural numbers as follows.\n\n" + desc,
        stub="def f (n : ℕ) : ℕ := sorry\n", solution=solution, free=["f"], tests=[test], examples=examples,
        meta={"values_tested": N})
