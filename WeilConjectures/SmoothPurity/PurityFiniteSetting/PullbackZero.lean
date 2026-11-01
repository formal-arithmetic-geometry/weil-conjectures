/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

/-! Recover the unnormalized derived pullback from the normalized ordinary pullback. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Ordinary restriction zero implies that the actual derived inverse-image morphism is zero.

Source: the normalized pullback definition, Stacks Tag 0G78.
(blueprint: lem-pur-closed-supported-cup-pullback-zero).

Proof: expand the normalized Hom map. Every comparison before and after the actual
inverse-image morphism is an isomorphism, including its shifted comparisons.
Cancel them successively; composition with an isomorphism preserves and reflects zero. -/
theorem closedSupportedCup_pullbackZero (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (i : Z ⟶ X) (a : ℕ) (t : ℤ)
    (α : P.FunctorialCupOrdinaryH true X (a : ℤ) t)
    (hα : P.functorialCupOrdinaryPullback true i
      (X ↘ Spec (.of P.field.k)) a t α = 0) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.map α = 0 := by
  unfold functorialCupOrdinaryPullback functorialCupNormalizedHom
    functorialCupExactHom at hα
  simpa only [Category.assoc, Preadditive.IsIso.comp_left_eq_zero,
    Preadditive.IsIso.comp_right_eq_zero, functorialCupInverseImage] using hα

end WeilConjectures.PurityFiniteSetting
