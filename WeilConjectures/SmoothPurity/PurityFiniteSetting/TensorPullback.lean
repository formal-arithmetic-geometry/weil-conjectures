/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-! Exact inverse image preserves the vanishing of a tensor factor. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The pullback of a tensor morphism with a killed first factor vanishes.

Source: Stacks Tag 07A4, naturality of the derived pullback-tensor comparison.
(blueprint: lem-pur-closed-supported-cup-tensor-pullback).

Proof: the canonical derived tensor comparison is natural in both variables. Conjugating
the pulled-back tensor morphism by its source and target comparisons gives the tensor
of the two pulled-back morphisms. Its first factor is zero by hypothesis. Additivity of
tensor makes that tensor morphism zero; invertibility of the comparisons proves the
claim. This statement concerns arbitrary derived objects and does not assert cup
vanishing or any closed-support detection result. -/
theorem closedSupportedCup_tensorPullbackFactor (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    {A B S : P.FunctorialCupDerived true X} (α : A ⟶ B)
    (hα : (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.map α = 0) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory.map
      (α ⊗ₘ (𝟙 S)) = 0 := by
  let F := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i
  let _ := F.mapDerivedCategoryOplaxMonoidal
  have hδ : IsIso (Functor.OplaxMonoidal.δ F.mapDerivedCategory B S) := by
    change IsIso ((F.mapDerivedCategoryTensorComparison.app B).app S)
    infer_instance
  apply (cancel_mono (Functor.OplaxMonoidal.δ F.mapDerivedCategory B S)).1
  rw [zero_comp, ← Functor.OplaxMonoidal.δ_natural]
  rw [hα]
  simp

end WeilConjectures.PurityFiniteSetting
