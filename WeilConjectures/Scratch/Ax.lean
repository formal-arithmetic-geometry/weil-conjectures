import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality
open Lean Meta Elab Command
partial def sorryDeps (root : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack := #[root]
  let mut res := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    let consts := (ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]))
    if consts.contains ``sorryAx then res := res.push n
    for c in consts do
      unless visited.contains c do stack := stack.push c
  return res
elab "#sorry_deps " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let r ← liftCoreM <| sorryDeps n
  logInfo m!"{n}: {r}"
#sorry_deps AlgebraicGeometry.Etale.dualizingComplexIdIso
