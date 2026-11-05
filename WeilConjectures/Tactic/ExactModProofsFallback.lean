/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Tactic.ExactModProofs

/-! # Minimal proof casts with a definitional-equality fallback

This variant first descends through matching applications to find the smallest
proof differences. If their arguments have different presentations, it compares
the enclosing application instead. All casts use ordinary equality proofs.
-/

public meta section

namespace ExactModProofs

open Lean Meta Elab Tactic

/-- Find minimal proof differences, allowing equal applications with unequal arguments. -/
partial def proofDiffsFallback (a b : Expr) (acc : Array (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  if a == b then return acc
  let leaf : MetaM (Array (Expr × Expr)) := do
    if !a.hasLooseBVars && !b.hasLooseBVars then
      if (← isProof a) then return acc.push (a, b)
      if (← isDefEq a b) then return acc
    throwError "exact_mod_proofs_fallback: the terms differ at{indentExpr a}\nand{indentExpr b}"
  match a, b with
  | .app .., .app .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size != bs.size || (fa != fb && !(fa.isLambda && fb.isLambda)) then return ← leaf
    try
      let mut acc ← if fa == fb then pure acc else proofDiffsFallback fa fb acc
      for i in [:as.size] do
        acc ← proofDiffsFallback as[i]! bs[i]! acc
      return acc
    catch _ => leaf
  | .lam _ ta ba _, .lam _ tb bb _ =>
    proofDiffsFallback ba bb (← proofDiffsFallback ta tb acc)
  | .forallE _ ta ba _, .forallE _ tb bb _ =>
    proofDiffsFallback ba bb (← proofDiffsFallback ta tb acc)
  | .letE _ ta va ba _, .letE _ tb vb bb _ =>
    proofDiffsFallback ba bb (← proofDiffsFallback va vb (← proofDiffsFallback ta tb acc))
  | .proj _ i sa, .proj _ j sb => if i == j then proofDiffsFallback sa sb acc else leaf
  | _, _ => leaf

/-- Close a goal by simultaneous proof-irrelevance casts with wrapper fallback. -/
def exactModProofsFallback (h : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let H := stripMData (← instantiateMVars (← inferType h))
    let G := stripMData (← instantiateMVars (← g.getType))
    let diffs ← proofDiffsFallback H G #[]
    let mut rep : Std.HashMap Expr Expr := {}
    for (a, b) in diffs do
      let ra := find rep a
      let rb := find rep b
      if ra != rb then rep := rep.insert rb ra
    let cs := rep.toArray.filterMap fun (c, _) ↦ if find rep c == c then none else some c
    if cs.isEmpty then
      g.assign h
      replaceMainGoal []
      return
    let rs := cs.map (find rep)
    let Ps ← cs.mapM fun c ↦ inferType c
    let (mH, mG) ← withLocalDeclsDND (Ps.map (`z, ·)) fun zs ↦ do
      return (← mkLambdaFVars zs (replaceAll H cs zs), ← mkLambdaFVars zs (replaceAll G cs zs))
    let eH ← congrProofs mH cs rs Ps
    let eG ← congrProofs mG cs rs Ps
    let h' := mkAppN (mkConst ``Eq.mp [.zero]) #[mkAppN mH cs, mkAppN mH rs, eH, h]
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkAppN mG rs).headBeta
    g.assign (mkAppN (mkConst ``Eq.mpr [.zero]) #[mkAppN mG cs, mkAppN mG rs, eG, g'])
    g'.mvarId!.assign h'
    replaceMainGoal []

/-- Cast only proof differences, with fallback for differently presented applications. -/
elab "exact_mod_proofs_fallback " h:term : tactic => withMainContext do
  exactModProofsFallback (← elabTerm h none)

end ExactModProofs
