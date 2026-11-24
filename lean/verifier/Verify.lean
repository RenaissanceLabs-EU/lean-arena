/-
Verify.lean: decides whether a submitted Lean module proves the theorems a task asked for.

  lean --run Verify.lean [--free a,b] [--native] <ReferenceModule> <SubmissionModule> <target>...

`--free a,b` names definitions the task asks the solver to write: their type must match the
reference, their value is the solver's own. `--native` additionally accepts the axioms that
`native_decide` introduces; it is used only for hidden test theorems the grader itself proves.

Both modules must already be compiled to .olean files on LEAN_PATH. This program imports only
`Lean`, never the submission, so nothing the submission declares (notation, macros, instances)
can change how the check itself is read. It loads the two modules into two separate environments
and compares kernel terms:

  1. every non-target constant the reference module declares (the task's own definitions) must be
     present in the submission with the same kind, type and value;
  2. every target must be present with exactly the reference type;
  3. the proof of every target may depend only on the three standard axioms.

It prints one JSON object per target and exits 0. The caller turns that into a reward.
-/
import Lean
open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- All axioms a constant depends on, found by walking every constant it mentions. -/
partial def axiomsOf (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut out : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => out := out.push (`missing ++ c)
    | some info =>
      let mut es : Array Expr := #[info.type]
      match info with
      | .axiomInfo _ => out := out.push c
      | .defnInfo v => es := es.push v.value
      | .thmInfo v => es := es.push v.value
      | .opaqueInfo v => es := es.push v.value
      | .ctorInfo v => todo := todo.push v.induct
      | .inductInfo v => for k in v.ctors do todo := todo.push k
      | .recInfo v => for r in v.rules do es := es.push r.rhs
      | .quotInfo _ => pure ()
      for e in es do
        for k in e.getUsedConstants do
          if !seen.contains k then todo := todo.push k
  return out

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def valueOf : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value | .opaqueInfo v => some v.value
  | _ => none

def sameDecl (a b : ConstantInfo) : Bool :=
  kindOf a == kindOf b && a.levelParams == b.levelParams && a.type == b.type && valueOf a == valueOf b

def jstr (s : String) : String := (Json.str s).compress

def isNativeAxiom (n : Name) : Bool :=
  n == ``Lean.ofReduceBool || n == ``Lean.trustCompiler ||
    n.components.any (fun c => c == `native_decide)

def isUnder (frees : List Name) (c : Name) : Bool := frees.any (fun f => f.isPrefixOf c)

partial def parseFlags (args : List String) (free : List Name) (native : Bool) :
    List Name × Bool × List String :=
  match args with
  | "--free" :: v :: rest => parseFlags rest (free ++ (v.splitOn ",").map String.toName) native
  | "--native" :: rest => parseFlags rest free true
  | rest => (free, native, rest)

def main (args : List String) : IO UInt32 := do
  let (free, native, args) := parseFlags args [] false
  match args with
  | refMod :: solMod :: targets =>
    initSearchPath (← findSysroot)
    let refName := refMod.toName
    let solName := solMod.toName
    let targetNames := targets.map String.toName
    let refEnv ← importModules #[{ module := refName }] {} (trustLevel := 0)
    let solEnv ← importModules #[{ module := solName }] {} (trustLevel := 0)
    -- 1. the task's own definitions are unchanged
    let some refIdx := refEnv.getModuleIdx? refName | throw (IO.userError "reference module not loaded")
    let mut tampered : Array Name := #[]
    for c in refEnv.header.moduleData[refIdx.toNat]!.constNames do
      if targetNames.contains c then continue
      let some r := refEnv.find? c | continue
      if free.contains c then
        match solEnv.find? c with
        | some s =>
          if r.levelParams != s.levelParams || r.type != s.type then tampered := tampered.push c
        | none => tampered := tampered.push c
        continue
      if isUnder free c then continue
      match solEnv.find? c with
      | some s => if !sameDecl r s then tampered := tampered.push c
      | none => tampered := tampered.push c
    for t in targetNames do
      let mut ok := true
      let mut why := ""
      match refEnv.find? t, solEnv.find? t with
      | none, _ => ok := false; why := "target missing from reference"
      | _, none => ok := false; why := "theorem not found in the submission"
      | some r, some s =>
        if !tampered.isEmpty then
          ok := false; why := s!"the task's definitions were changed or are missing: {tampered.toList}"
        else if kindOf s != "theorem" && kindOf s != "def" then
          ok := false; why := s!"declared as {kindOf s}, not proved"
        else if r.levelParams != s.levelParams || r.type != s.type then
          ok := false; why := "the statement differs from the one asked for"
        else
          let ax := axiomsOf solEnv t
          let bad := ax.filter (fun a => !allowedAxioms.contains a && !(native && isNativeAxiom a))
          if !bad.isEmpty then
            ok := false; why := s!"depends on axioms that are not allowed: {bad.toList}"
      IO.println s!"\{\"target\": {jstr t.toString}, \"ok\": {ok}, \"why\": {jstr why}}"
    return 0
  | _ =>
    IO.eprintln "usage: lean --run Verify.lean [--free a,b] [--native] <ReferenceModule> <SubmissionModule> <target>..."
    return 2
