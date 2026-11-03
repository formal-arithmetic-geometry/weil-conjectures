/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineDiagonalData
/-! # The two presentations of canonical diagonal chart transport -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors derivedUpperStarLowerStarAdjunction
-- Compare recorded instances without expanding the derived localization constructions.
private meta def unfoldBoundary (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
  if let .fvar id := e then
    if let some v := (← id.getDecl).value? then return some v
  if let .letE _ _ v b _ := e then return some (b.instantiate1 v)
  let names : List Lean.Name := [``DerivedCategoryModule, ``ordinaryFinitePushforward,
    ``ordinaryFinitePullback, ``ordinaryFiniteP1DiagonalTarget,
    ``ordinaryFiniteP1DiagonalChartMap, ``ordinaryFiniteChartTransport,
    ``ordinaryFiniteAdjunction, ``projectiveLineDiagonalChartPushforward]
  if let some n := e.getAppFn.constName? then
    if names.contains n then
      return ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e)
  return none

/-- Both chart maps use the canonical derived adjunction and the same composition
and shifted-line comparisons. Source: blueprint diagonal integral chart identification.
(blueprint: lem-amb-p1-diagonal-chart-comparison)
Proof: expand the recorded chart maps and recorded adjunction. Their four factors
are definitionally identical; proof irrelevance identifies invertibility witnesses. -/
theorem projectiveLineDiagonalChartPushforward_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    projectiveLineDiagonalChartPushforward N hN A hA S hS a =
      ordinaryFiniteP1DiagonalChartMap A N hA
        (projectiveLineTraceTransport N hN A hA) S hS a := by
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let some (_, lhs, rhs) := (← g.getType).eq? | throwError "expected an equality"
      let h ← structuralHEq 200 lhs rhs
      g.assign (← Lean.Meta.mkAppM ``eq_of_heq #[h])
    Lean.Elab.Tactic.replaceMainGoal []
end AlgebraicGeometry.Etale
