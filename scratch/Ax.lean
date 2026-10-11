import WeilConjectures.SixFunctors.Etale.Derived.Orientation
open Lean Elab Command in
elab "#sorry_deps " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let mut visited : NameSet := {}
  let mut stack := [n]
  let mut res : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if visited.contains c then continue
    visited := visited.insert c
    let some ci := env.find? c | continue
    let consts := ci.getUsedConstantsAsSet
    if consts.contains ``sorryAx then res := res.push c
    for d in consts do
      if !visited.contains d then stack := d :: stack
  logInfo m!"{res}"
#sorry_deps AlgebraicGeometry.Etale.Orientation.nonempty_iso_verdierDual_coefficientDual
