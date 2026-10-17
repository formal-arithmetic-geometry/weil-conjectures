module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public meta import Lean

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
  [IsSeparated f]
open Lean Elab Command Meta Term in
meta partial def exprDiff (a b : Expr) (depth : Nat := 0) : MetaM Unit := do
  if a == b then return
  if depth > 200 then return
  if (← isProof a) then
    let ta ← instantiateMVars (← inferType a)
    let tb ← instantiateMVars (← inferType b)
    if ta != tb then
      logInfo m!"PROOF types differ at {depth}"
      exprDiff ta tb (depth+1)
    return
  match a, b with
  | .app f x, .app g y =>
    if f == g then exprDiff x y (depth+1)
    else if x == y then exprDiff f g (depth+1)
    else do
      exprDiff f g (depth+1)
      exprDiff x y (depth+1)
  | .mdata _ a', _ => exprDiff a' b depth
  | _, .mdata _ b' => exprDiff a b' depth
  | _, _ =>
    logInfo m!"DIFF at depth {depth}:\n{a}\n=====\n{b}"

open Lean Meta in
meta def unfoldDCM (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if e.isAppOfArity ``AlgebraicGeometry.Etale.DerivedCategoryModule 3 then
      match ← unfoldDefinition? e with
      | some e' => return .visit e'
      | none => return .continue
    else return .continue)



end Etale

end AlgebraicGeometry

open Lean Elab Tactic Meta in
elab "cmp_goal " t:term : tactic => withMainContext do
  let e ← Term.elabTerm t none
  let ty ← (instantiateMVars (← inferType e))
  let g ← (instantiateMVars (← getMainTarget))
  logInfo m!"equal: {ty == g}"
  AlgebraicGeometry.Etale.exprDiff ty g
  logInfo m!"done"
