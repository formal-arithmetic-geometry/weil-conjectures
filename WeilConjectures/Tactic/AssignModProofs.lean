/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `assign_mod_proofs`

`assign_mod_proofs h` closes the goal `G` with a term `h : H`, where `H` and `G` are expected to be
syntactically equal up to proofs and to definitional unfoldings which are cheap for the kernel.
It is meant for instantiating abstract lemmas at large concrete composites (of derived functors,
say), where `H` is the statement of a concrete lemma and `G` the instantiated hypothesis of the
abstract lemma.

Two kinds of differences between `H` and `G` make the kernel slow there:

* proofs inside instance arguments, e.g. two elaborations of the same `Prop`-valued instance, one
  of them an auxiliary proof constant: the instances, hence the categories, differ syntactically,
  and the kernel unfolds compositions and morphisms to compare them;
* checking that `G` itself is well-typed (as the kernel does for `mkExpectedTypeHint h G`), since
  the implicit arguments of an instantiated abstract statement only agree with the types of the
  concrete terms up to unfolding.

The tactic avoids both: at each pair of differing proofs `p : P` (of `H`) and `q` (of `G`) at
corresponding positions, it casts `h` along `fun x : P ↦ H[p := x]` (a motive built from `H`, which
is well-typed) and the equation `p = q` (by proof irrelevance), and finally assigns the goal to the
casted term without any check by the elaborator. The comparison of the resulting type with `G`,
now syntactically equal at all proof positions, is left to the kernel.
-/

public meta section

namespace AssignModProofs

open Lean Meta Elab Tactic

/-- Syntactic equality of `a` and `b` up to proofs. -/
partial def eqUpToProofs (a b : Expr) : MetaM Bool := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return true
  if ← (try isProof a catch _ => pure false) then
    return ← (try isProof b catch _ => pure false)
  if a.isApp && b.isApp then
    let as := a.getAppArgs
    let bs := b.getAppArgs
    unless as.size == bs.size do return false
    unless ← eqUpToProofs a.getAppFn b.getAppFn do return false
    for i in [:as.size] do
      unless ← eqUpToProofs as[i]! bs[i]! do return false
    return true
  return false

/-- Whether the proofs `a` and `b` (closed) prove the same proposition, up to proofs or to a cheap
unfolding (instance transparency, bounded). -/
def sameProp (a b : Expr) : MetaM Bool := do
  unless ← (try isProof b catch _ => pure false) do return false
  let ta ← inferType a
  let tb ← inferType b
  if ← eqUpToProofs ta tb then return true
  try
    withTransparency .instances <| withOptions (fun o ↦ o.set `maxHeartbeats (20000 : Nat)) <|
      withCurrHeartbeats (isDefEq ta tb)
  catch _ => return false

/-- The first pair of differing proofs of the same proposition at corresponding positions of `a`
and `b` (a parallel traversal of applications with the same head and number of arguments). -/
partial def firstProofPair (a b : Expr) : MetaM (Option (Expr × Expr)) := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return none
  if !a.hasLooseBVars && !b.hasLooseBVars && (← (try isProof a catch _ => pure false)) then
    return if ← sameProp a b then some (a, b) else none
  if a.isApp && b.isApp then
    let as := a.getAppArgs
    let bs := b.getAppArgs
    let fa := a.getAppFn.consumeMData
    let fb := b.getAppFn.consumeMData
    if as.size == bs.size &&
        (fa == fb || (fa.isConst && fb.isConst && fa.constName! == fb.constName!)) then
      for i in [:as.size] do
        if let some r ← firstProofPair as[i]! bs[i]! then return some r
  return none

/-- Replace by `x` the occurrences of `p` in `a` at the positions where `b` has `q`. -/
partial def replaceProof (a b p q x : Expr) : Expr :=
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then a
  else if a == p && b == q then x
  else if a.isApp && b.isApp then
    let as := a.getAppArgs
    let bs := b.getAppArgs
    let fa := a.getAppFn.consumeMData
    let fb := b.getAppFn.consumeMData
    if as.size == bs.size &&
        (fa == fb || (fa.isConst && fb.isConst && fa.constName! == fb.constName!)) then
      mkAppN a.getAppFn (Array.ofFn fun (i : Fin as.size) ↦ replaceProof as[i] bs[i]! p q x)
    else a
  else a

/-- Close the goal with `h`, after casting `h` so that its proofs agree with the goal's. -/
def assignModProofs (h : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let G ← instantiateMVars (← g.getType)
    let mut e ← instantiateMVars h
    let mut H ← instantiateMVars (← inferType e)
    while true do
      let some (p, q) ← firstProofPair H G | break
      let P ← inferType p
      let motive ← withLocalDeclD `x P fun x ↦ mkLambdaFVars #[x] (replaceProof H G p q x)
      let eq := mkApp6 (mkConst ``congrArg [.zero, .succ .zero]) P (.sort .zero) p q motive
        (mkApp3 (mkConst ``proof_irrel) P p q)
      e := mkApp4 (mkConst ``Eq.mp [.zero]) (mkApp motive p) (mkApp motive q) eq e
      H := motive.beta #[q]
    g.assign e
    replaceMainGoal []

/-- `assign_mod_proofs h` closes the goal with `h`, whose type agrees with the goal up to proofs
and to unfoldings left to the kernel (see the module docstring). The elaborator does not check
the result: an error, if any, is reported by the kernel. -/
elab "assign_mod_proofs " h:term : tactic => withMainContext do
  let e ← elabTerm h none
  Term.synthesizeSyntheticMVarsNoPostponing
  assignModProofs e

end AssignModProofs
