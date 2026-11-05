/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public meta import WeilConjectures.Tactic.ExactModProofs
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# `cast_proofs_trace`: `cast_proofs` with a report of the non-proof differences

Diagnostic variant of `cast_proofs`: every pair of closed, differing, non-proof subterms which is
left to the kernel (compared by `isDefEq`) is reported with `logInfo`, so that kernel timeouts of
`cast_proofs` can be attributed to the definitional unfolding of a specific pair.
-/

public meta section

namespace ExactModProofs

open Lean Meta Elab Tactic

/-- As `proofPairs`, reporting the definitionally equal non-proof leaves. -/
partial def proofPairsTrace (a b : Expr) (acc : Array (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  if a == b then return acc
  if !a.hasLooseBVars && !b.hasLooseBVars && (← isProof a) then return acc.push (a, b)
  let leaf : MetaM (Array (Expr × Expr)) := do
    if !a.hasLooseBVars && !b.hasLooseBVars then
      if (← withReducible (isDefEq a b)) then
        logInfo m!"cast_proofs_trace: reducibly defeq leaf{indentExpr a}\nvs{indentExpr b}"
        return acc
      if (← isDefEq a b) then
        logInfo m!"cast_proofs_trace: DEFAULT-defeq leaf (kernel will unfold){indentExpr a}\nvs{indentExpr b}"
        return acc
    throwError "cast_proofs_trace: the terms differ at{indentExpr a}\nand{indentExpr b}"
  match a, b with
  | .app .., .app .. =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let as := a.getAppArgs
    let bs := b.getAppArgs
    if as.size != bs.size || (fa != fb && !(fa.isLambda && fb.isLambda)) then return ← leaf
    try
      let mut acc ← if fa == fb then pure acc else proofPairsTrace fa fb acc
      for i in [:as.size] do
        acc ← proofPairsTrace as[i]! bs[i]! acc
      return acc
    catch _ => leaf
  | .lam _ ta ba _, .lam _ tb bb _ => proofPairsTrace ba bb (← proofPairsTrace ta tb acc)
  | .forallE _ ta ba _, .forallE _ tb bb _ => proofPairsTrace ba bb (← proofPairsTrace ta tb acc)
  | .letE _ ta va ba _, .letE _ tb vb bb _ =>
    proofPairsTrace ba bb (← proofPairsTrace va vb (← proofPairsTrace ta tb acc))
  | .proj _ i sa, .proj _ j sb => if i == j then proofPairsTrace sa sb acc else leaf
  | _, _ => leaf

/-- As `castProofs`, with the report of `proofPairsTrace`. -/
def castProofsTrace (h : Expr) : TacticM Unit := do
  let mut g ← getMainGoal
  let H := stripMData (← instantiateMVars (← inferType h))
  let mut G := stripMData (← instantiateMVars (← g.getType))
  g ← g.replaceTargetDefEq G
  let mut round : Nat := 0
  for _ in [:20] do
    let diffs ← proofPairsTrace H G #[]
    logInfo m!"cast_proofs_trace: round {round}: {diffs.size} proof pairs"
    if round == 0 then
      let mut k : Nat := 0
      for (a, b) in diffs do
        if k < 60 then
          let ta ← inferType a
          let tb ← inferType b
          logInfo m!"cast_proofs_trace: proof pair {k}:{indentExpr a}\n  : {ta}\nvs{indentExpr b}\n  : {tb}"
          if k < 8 then
            logInfo m!"cast_proofs_trace: raw pair {k}:\n{(toString a.dbgToString).take 2500}\nRAWvs\n{(toString b.dbgToString).take 2500}"
        k := k + 1
    round := round + 1
    if diffs.isEmpty then break
    let mut pairs : Array (Expr × Expr) := #[]
    for p in diffs do
      unless pairs.contains p do pairs := pairs.push p
    for (a, b) in pairs do
      let Pb ← inferType b
      let motive ← withLocalDeclD `z Pb fun z ↦ mkLambdaFVars #[z] (abstractPair G H a b z)
      let eq := mkApp3 (mkConst ``proof_irrel) Pb b a
      let propEq := mkAppN (mkConst ``congrArg [.zero, .succ .zero])
        #[Pb, .sort .zero, b, a, motive, eq]
      let G' := motive.beta #[a]
      let next ← mkFreshExprSyntheticOpaqueMVar G'
      g.assign (mkAppN (mkConst ``Eq.mpr [.zero]) #[G, G', propEq, next])
      g := next.mvarId!
      G := G'
  g.assign h
  replaceMainGoal []

/-- `cast_proofs_trace h`: `cast_proofs h` reporting the non-proof differences left to the
kernel. -/
elab "cast_proofs_trace " h:term : tactic => withMainContext do
  castProofsTrace (← elabTerm h none)

end ExactModProofs

namespace ExactModProofs

open Lean Meta Elab Tactic

/-- `exact_kernel h` closes the goal with `h` WITHOUT any elaborator-side definitional check: the
goal is assigned `h` directly and the kernel compares the two types (proof irrelevance and the
unfolding of reducible abbreviations are native and cheap in the kernel; no cast motives are
produced). Use when `exact h` makes the unifier unfold large definitions and `cast_proofs h`
produces hundreds of casts. -/
elab "exact_kernel " h:term : tactic => withMainContext do
  let g ← getMainGoal
  let h ← elabTerm h none
  let h ← instantiateMVars h
  g.assign h
  replaceMainGoal []

end ExactModProofs
