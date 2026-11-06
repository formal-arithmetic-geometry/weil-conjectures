import WeilConjectures.LeanEval.WeilConjectures

/-!
# Sweep for declarations mixing the two `IsGrothendieckAbelian (ModuleCat R)` instances

Computes the dependency closure (through types and values) of
`LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures` and lists every constant in it
whose type or value mentions both the shortcut instance
`ModuleCat.isGrothendieckAbelian_of_commRing` and Mathlib's
`instIsGrothendieckAbelianModuleCat`. Such proofs can make the kernel unfold derived-category
constructions to identify the two instances (this stalled the lean-eval comparator).

Not imported by the library. Run with `lake lean scripts/instance_mix_sweep.lean`.

For each hit it prints the name, the module, where the two instances occur (`type`/`value`),
the number of distinct subterms of the value (sharing-aware DAG size), the tree size without
sharing, and `Expr.approxDepth`. Hits are sorted by DAG size, largest first.
-/

open Lean

namespace InstanceMixSweep

/-- Number of distinct subterms (sharing-aware size) and tree size without sharing. -/
def sizes (e : Expr) : Nat × Nat := Id.run do
  let mut seen : Std.HashMap Expr Nat := {}
  let mut stack : Array (Expr × Bool) := #[(e, false)]
  while h : stack.size > 0 do
    let (e, done) := stack.back
    stack := stack.pop
    if seen.contains e then continue
    let children : Array Expr := match e with
      | .app f a => #[f, a]
      | .lam _ t b _ | .forallE _ t b _ => #[t, b]
      | .letE _ t v b _ => #[t, v, b]
      | .mdata _ b | .proj _ _ b => #[b]
      | _ => #[]
    if done then
      let s := children.foldl (fun acc c => acc + seen.getD c 0) 1
      seen := seen.insert e s
    else
      stack := stack.push (e, true)
      for c in children do
        unless seen.contains c do stack := stack.push (c, false)
  return (seen.size, seen.getD e 0)

def shortcut : Name := `ModuleCat.isGrothendieckAbelian_of_commRing
def mathlibInst : Name := `instIsGrothendieckAbelianModuleCat
def root : Name := `LeanEval.AlgebraicGeometry.WeilConjectures.weil_conjectures

def mentions (e : Expr) : Bool × Bool :=
  let s := e.getUsedConstantsAsSet
  (s.contains shortcut, s.contains mathlibInst)

def run : CoreM Unit := do
  let env ← getEnv
  for n in [shortcut, mathlibInst, root] do
    unless env.contains n do throwError "missing constant {n}"
  -- dependency closure of `root` through types and values
  let mut visited : NameSet := {}
  let mut todo : Array Name := #[root]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    for m in ci.getUsedConstantsAsSet do
      unless visited.contains m do todo := todo.push m
  let mut hits : Array (Name × Name × String × Nat × Nat × Nat) := #[]
  for n in visited do
    let some ci := env.find? n | continue
    let (ts, tm) := mentions ci.type
    let (vs, vm) := match ci.value? (allowOpaque := true) with
      | some v => mentions v
      | none => (false, false)
    unless (ts || vs) && (tm || vm) do continue
    let mod := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!
      | none => `_current
    let wh := s!"shortcut:{if ts then "type " else ""}{if vs then "value" else ""} \
      mathlib:{if tm then "type " else ""}{if vm then "value" else ""}"
    let v := (ci.value? (allowOpaque := true)).getD ci.type
    let (dag, tree) := sizes v
    hits := hits.push (n, mod, wh, dag, tree, v.approxDepth.toNat)
  hits := hits.qsort (fun a b => a.2.2.2.1 > b.2.2.2.1)
  IO.println s!"closure size: {visited.size}"
  IO.println s!"constants using both instances: {hits.size}"
  IO.println "name | module | occurrences | dag size | tree size | approxDepth"
  for (n, mod, wh, dag, tree, d) in hits do
    IO.println s!"{n} | {mod} | {wh} | {dag} | {tree} | {d}"

end InstanceMixSweep

#eval InstanceMixSweep.run
