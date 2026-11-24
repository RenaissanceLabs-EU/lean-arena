#!/usr/bin/env python3
"""Count Mathlib theorems per MSC area, and read Mathlib's own coverage lists.

Writes data/coverage.json. The mapping from Mathlib directories to MSC2020 areas is by hand
(PREFIXES below, longest prefix wins); a directory can feed several areas, and the count is
shared evenly. Counts are `theorem` and `lemma` declarations found by a line pattern, a proxy
for size, not an exact count of formal statements.
"""
import json, os, re, subprocess, collections, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ML = os.path.join(ROOT, "lean/.lake/packages/mathlib")
PREFIXES = {
 "Logic": ["03"], "Order/Filter": ["54"], "Order": ["06"], "SetTheory": ["03"], "ModelTheory": ["03"], "Computability": ["03", "68"],
 "Data/Set": ["03"], "Data/Finset": ["05"], "Data/Fintype": ["05"], "Data/Multiset": ["05"], "Data/List": ["68"], "Data/Nat": ["11"], "Data/Int": ["11"],
 "Data/Rat": ["11"], "Data/Real": ["26"], "Data/ENNReal": ["28"], "Data/EReal": ["26"], "Data/Complex": ["30"], "Data/Matrix": ["15"], "Data/Fin": ["05"],
 "Data/ZMod": ["11"], "Data/Finsupp": ["13"], "Data/DFinsupp": ["13"], "Data/Seq": ["68"], "Data": ["68"],
 "Algebra/Group": ["20"], "Algebra/GroupWithZero": ["20"], "Algebra/Ring": ["16"], "Algebra/Field": ["12"], "Algebra/Order": ["06"], "Algebra/Polynomial": ["12"],
 "Algebra/MvPolynomial": ["13"], "Algebra/BigOperators": ["05"], "Algebra/Homology": ["18"], "Algebra/Category": ["18"], "Algebra/Lie": ["17"], "Algebra/Module": ["13", "15"],
 "Algebra/Algebra": ["16"], "Algebra/Star": ["46"], "Algebra/MonoidAlgebra": ["16"], "Algebra/Order/Floor": ["11"], "Algebra/CharP": ["12"], "Algebra/Quaternion": ["16"], "Algebra": ["08"],
 "GroupTheory": ["20"], "RingTheory/Polynomial": ["13"], "RingTheory/Ideal": ["13"], "RingTheory/DedekindDomain": ["13", "11"], "RingTheory/Valuation": ["13", "12"],
 "RingTheory/PowerSeries": ["13"], "RingTheory/MvPowerSeries": ["13"], "RingTheory/Localization": ["13"], "RingTheory/Spectrum": ["13", "14"], "RingTheory/WittVector": ["13", "11"],
 "RingTheory/HahnSeries": ["13"], "RingTheory/GradedAlgebra": ["13"], "RingTheory": ["13", "16"],
 "FieldTheory": ["12"], "LinearAlgebra": ["15"], "LinearAlgebra/AffineSpace": ["51"], "LinearAlgebra/RootSystem": ["17"], "LinearAlgebra/QuadraticForm": ["11", "15"],
 "RepresentationTheory": ["20", "16"], "CategoryTheory": ["18"], "AlgebraicGeometry": ["14"], "AlgebraicTopology": ["55"], "Condensed": ["18", "55"],
 "NumberTheory/ModularForms": ["11", "30"], "NumberTheory/LSeries": ["11"], "NumberTheory/NumberField": ["11", "12"], "NumberTheory/Padics": ["11"], "NumberTheory": ["11"],
 "Combinatorics/SimpleGraph": ["05"], "Combinatorics/Matroid": ["05"], "Combinatorics/Additive": ["11", "05"], "Combinatorics/Enumerative": ["05"], "Combinatorics": ["05"],
 "Analysis/SpecialFunctions": ["33", "26"], "Analysis/Calculus": ["26", "58"], "Analysis/Normed": ["46"], "Analysis/NormedSpace": ["46"], "Analysis/Convex": ["52", "46"], "Analysis/InnerProductSpace": ["46", "47"],
 "Analysis/Complex": ["30"], "Analysis/CStarAlgebra": ["46"], "Analysis/Analytic": ["30", "32"], "Analysis/Asymptotics": ["41", "26"], "Analysis/BoxIntegral": ["28", "26"], "Analysis/Distribution": ["46"],
 "Analysis/LocallyConvex": ["46"], "Analysis/Fourier": ["42"], "Analysis/Real": ["26"], "Analysis/RCLike": ["46"], "Analysis/ODE": ["34"], "Analysis/SpecificLimits": ["40"], "Analysis/PSeries": ["40"], "Analysis/Subadditive": ["40"], "Analysis": ["26"],
 "MeasureTheory": ["28"], "Probability": ["60"], "InformationTheory": ["94"], "Dynamics": ["37"], "Control": ["93"],
 "Topology/Algebra": ["22", "54"], "Topology/MetricSpace": ["54"], "Topology/Category": ["54", "18"], "Topology/Homotopy": ["55"], "Topology/CWComplex": ["57"], "Topology": ["54"],
 "Geometry/Manifold": ["58", "57"], "Geometry/Euclidean": ["51"], "Geometry/Convex": ["52"], "Geometry/Group": ["20"], "Geometry": ["51"],
 "Mathport": [], "Tactic": [], "Util": [], "Lean": [], "Testing": [], "Deprecated": [], "Init": [],
}
pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|nonrec\s+)*(?:theorem|lemma)\s", re.M)

def prefix_for(rel):
    parts = rel.split("/")
    for k in range(len(parts) - 1, 0, -1):
        key = "/".join(parts[:k])
        if key in PREFIXES: return PREFIXES[key]
    return []

def main():
    msc = {a["code"]: a for a in json.load(open(os.path.join(ROOT, "data/msc.json"), encoding="utf-8"))}
    thm = collections.defaultdict(float); files = collections.defaultdict(float); dirs = collections.defaultdict(collections.Counter)
    unmapped = collections.Counter(); total = 0
    for dp, _, fs in os.walk(os.path.join(ML, "Mathlib")):
        for f in fs:
            if not f.endswith(".lean"): continue
            p = os.path.join(dp, f); rel = os.path.relpath(p, os.path.join(ML, "Mathlib"))
            n = len(pat.findall(open(p, encoding="utf-8").read())); total += n
            areas = prefix_for(rel[:-5])
            if not areas:
                if not rel.startswith(("Tactic", "Util", "Lean", "Mathport", "Testing", "Deprecated", "Init")): unmapped[rel.split("/")[0]] += n
                continue
            for a in areas:
                thm[a] += n / len(areas); files[a] += 1.0 / len(areas)
                dirs[a]["/".join(rel.split("/")[:2]) if "/" in rel else rel[:-5]] += n / len(areas)
    sha = subprocess.run(["git", "-C", ML, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    # Mathlib's own lists
    import yaml
    D = os.path.join(ML, "docs")
    def formal(v): return bool(v.get("decl") or v.get("decls"))
    y100 = yaml.safe_load(open(os.path.join(D, "100.yaml"), encoding="utf-8"))
    l100 = []
    for k, v in y100.items():
        decl = v.get("decl") or (v.get("decls") or [None])[0]
        l100.append({"n": int(k), "title": str(v.get("title", "")).strip(), "formalized": formal(v) or bool(v.get("links")),
                     "in_mathlib": formal(v), "decl": decl, "authors": v.get("authors", "")})
    y1000 = yaml.safe_load(open(os.path.join(D, "1000.yaml"), encoding="utf-8"))
    n1000 = len(y1000); f1000 = sum(1 for v in y1000.values() if formal(v))
    def curriculum(fn):
        out = []
        for topic, secs in yaml.safe_load(open(os.path.join(D, fn), encoding="utf-8")).items():
            tot = have = 0
            for sec, items in secs.items():
                if not isinstance(items, dict): continue
                for name, val in items.items():
                    tot += 1
                    if val and not str(val).startswith("http") and str(val).strip(): have += 1
            out.append({"topic": topic, "items": tot, "in_mathlib": have})
        return out
    areas = {}
    for c in sorted(msc):
        areas[c] = {"theorems": round(thm.get(c, 0)), "modules": round(files.get(c, 0)),
                    "dirs": [{"dir": d, "theorems": round(n)} for d, n in dirs[c].most_common(4)]}
    out = {"mathlib_commit": sha, "mathlib_theorems": total, "mathlib_modules": int(sum(files.values())), "areas": areas,
           "unmapped": dict(unmapped.most_common(8)),
           "hundred": l100, "thousand": {"listed": n1000, "in_mathlib": f1000},
           "undergrad": curriculum("undergrad.yaml"), "overview": curriculum("overview.yaml")}
    json.dump(out, open(os.path.join(ROOT, "data/coverage.json"), "w"), indent=1, ensure_ascii=False)
    print("theorems", total, "mapped", round(sum(thm.values())), "unmapped", dict(unmapped.most_common(8)))
    top = sorted(areas.items(), key=lambda x: -x[1]["theorems"])
    print([(c, a["theorems"]) for c, a in top[:12]])
    print("areas with zero:", [c for c, a in areas.items() if a["theorems"] == 0])
    print("100:", sum(1 for x in l100 if x["formalized"]), "/", len(l100), " 1000+:", f1000, "/", n1000)


if __name__ == "__main__":
    main()
