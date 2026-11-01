/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBundle
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric

/-! # Ordinary normalization of coefficient-first vector integration
Source: blueprint vector-bundle purity, ordinary integration and its adjunction transpose.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

attribute [local implicit_reducible] Scheme.Modules

attribute [local irreducible] Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction

-- Retain the native finite-coefficient presentations when specializing the calculation.
open WeilConjectures.PurityFiniteSetting in
set_option linter.defProp false in
private theorem hpi_congr {α β : Sort v} {p : α → Sort w} {q : β → Sort w}
    (ht : α = β) (h : ∀ a b, HEq a b → p a = q b) :
    (∀ a, p a) = (∀ b, q b) := by
  cases ht
  have hpq : p = q := funext fun a ↦ h a a HEq.rfl
  cases hpq
  rfl

private theorem hfunext {α β : Sort v} {P : α → Sort w} {Q : β → Sort w}
    {f : ∀ a, P a} {g : ∀ b, Q b} (ht : α = β)
    (hPQ : ∀ a b, HEq a b → P a = Q b)
    (h : ∀ a b, HEq a b → HEq (f a) (g b)) : HEq f g := by
  cases ht
  have hPQ' : P = Q := funext fun a ↦ hPQ a a HEq.rfl
  cases hPQ'
  apply heq_of_eq
  funext a
  exact eq_of_heq (h a a HEq.rfl)

-- Build the definitional comparison by cached heterogeneous congruence.
-- Each step is an ordinary equality proof checked by the kernel. Keeping repeated
-- instance comparisons shared avoids unfolding the native tensor constructions.
open Lean Meta Elab Tactic in
private meta def expandProjection (e : Expr) : MetaM Expr := do
  let .proj n i receiver := e.getAppFn | return e
  let some info := getStructureInfo? (← getEnv) n | return e
  let field := n ++ info.fieldNames[i]!
  return mkAppN (← mkAppM field #[receiver]) e.getAppArgs

open Lean Meta Elab Tactic in
private meta partial def structuralRefl (g : MVarId) (fuel : Nat) :
    StateRefT (ExprMap Expr) MetaM Unit :=
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    if let some proof := (← get).get? target then
      g.assign proof
      return
    let h ← mkFreshExprSyntheticOpaqueMVar target
    structuralReflCore h.mvarId! fuel
    let proof ← instantiateMVars h
    if proof.hasMVar || proof.hasSorry then
      throwError "incomplete structural congruence"
    modify fun cache => cache.insert target proof
    g.assign proof
where
  structuralReflCore (g : MVarId) (fuel : Nat) :
      StateRefT (ExprMap Expr) MetaM Unit := g.withContext do
    if fuel == 0 then throwError "structural reflexivity exhausted"
    let target ← g.getType
    try
      g.assumption
      return
    catch _ => pure ()
    let (lhs, rhs) ←
      if let some (_, lhs, rhs) := target.eq? then pure (lhs, rhs)
      else if let some (_, lhs, _, rhs) := target.heq? then pure (lhs, rhs)
      else throwError "expected equality"
    if lhs == rhs then
      if target.isHEq then g.assign (← mkHEqRefl lhs)
      else g.assign (← mkEqRefl lhs)
    else if (← isProof lhs) && (← isProof rhs) then
      let proof ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      let proof ← if target.isHEq then pure proof else mkEqOfHEq proof
      g.assign proof
    else if lhs.isForall && rhs.isForall then
      let ge ← g.heqOfEq
      let gs ← ge.apply (← mkConstWithFreshMVarLevels ``hpi_congr)
      match gs with
      | [ht, hb] =>
        structuralRefl ht (fuel - 1)
        let (_, hb) ← hb.intro1
        let (_, hb) ← hb.intro1
        let (_, hb) ← hb.intro1
        structuralRefl hb (fuel - 1)
      | _ => throwError "Unexpected heterogeneous forall goals"
    else if lhs.isLambda && rhs.isLambda then
      let gh ← g.eqOfHEq
      let gs ← gh.apply (← mkConstWithFreshMVarLevels ``hfunext)
      match gs with
      | [ht, hPQ, hb] =>
        structuralRefl ht (fuel - 1)
        for h in [hPQ, hb] do
          let (_, h) ← h.intro1
          let (_, h) ← h.intro1
          let (_, h) ← h.intro1
          structuralRefl h (fuel - 1)
      | _ => throwError "Unexpected heterogeneous function goals"
    else if lhs.isApp && lhs.getAppFn == rhs.getAppFn then
      let gh ← g.eqOfHEq
      let ct ← mkHCongrWithArity lhs.getAppFn lhs.getAppNumArgs
      let cp ← abstractProof ct.proof
      let gs ← gh.apply cp { synthAssignedInstances := false }
      for h in gs do structuralRefl h (fuel - 1)
    else
      let lhs' ← expandProjection lhs
      let rhs' ← expandProjection rhs
      let lhs' ← if lhs' == lhs then withTransparency .all (whnf lhs) else pure lhs'
      let rhs' ← if rhs' == rhs then withTransparency .all (whnf rhs) else pure rhs'
      if lhs' == lhs && rhs' == rhs then
        g.refl
      else
        let ty ← if target.isHEq then mkHEq lhs' rhs' else mkEq lhs' rhs'
        let h ← mkFreshExprSyntheticOpaqueMVar ty
        g.assign h
        structuralRefl h.mvarId! (fuel - 1)

open Lean Meta Elab Tactic in
local elab "structural_rfl" : tactic => do
  let _ ← (structuralRefl (← getMainGoal) 100).run {}
  replaceMainGoal []

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
