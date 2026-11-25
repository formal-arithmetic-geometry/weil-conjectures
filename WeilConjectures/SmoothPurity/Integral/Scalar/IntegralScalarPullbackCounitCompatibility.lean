/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons

import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The scalar pullback square before total derived limit -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem scalarCounitPrimeUnit (l : ℕ) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] : IsUnit (l : Γ(X, ⊤)) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have h : IsUnit (l : X.presheaf.stalk x) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x)).ne_zero
  simpa only [map_natCast] using h

private noncomputable def scalarCounitModels
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : IntegralComparisonCoefficientData l E) (W : Bool → Scheme.{u})
    (M : CompletedOperations.Models l E W) : CompletedOperations.Models l E W where
  calculus := fun a ↦ D.system (W a)
  system := M.system
  completion := fun a ↦ M.completion a ≪≫ Functor.isoWhiskerRight
    (Adjunction.leftAdjointUniq (M.calculus a).adjunction (D.system (W a)).adjunction)
      (coefficientSequenceLimit l E (W a))
  completion_unit := by
    intro a K
    dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app]
    rw [← Category.assoc, M.completion_unit]
    exact Adjunction.unit_leftAdjointUniq_hom_app _ _ K
  roos := fun a ↦ D.roos (W a)
  pullback := fun f ↦ D.pullback f

/-- The prescribed scalar/pullback map satisfies the square of actual counits in
whole-system reduction coordinates. -/
theorem integralScalarPullbackCounit_compatibility
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (C : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (hF : IsSfDerivedComplete l E X ((integralDerivedPullback l E f).obj K.obj)) :
    ((C.coefficient L).system X).reduction.map
        (scalarPullbackCompleted l E L ι f K.obj K.property.1 hF).hom ≫
      (integralComparisonPullbackCounit l L f
        ((C.coefficient L).system Y) ((C.coefficient L).system X)
        ((C.coefficient L).roos X) ((C.coefficient L).pullback f)).app
          ((integralScalarExtension l E L ι Y).obj K.obj) ≫
      (integralComparisonDerivedSequencePullback l L f).map
        ((integralComparisonScalarCounit l E L ι Y
          ((C.coefficient E).system Y) ((C.coefficient L).system Y)
          ((C.coefficient L).roos Y) ((C.scalar E L ι).model Y)).app K.obj) =
    (integralComparisonScalarCounit l E L ι X
        ((C.coefficient E).system X) ((C.coefficient L).system X)
        ((C.coefficient L).roos X) ((C.scalar E L ι).model X)).app
          ((integralDerivedPullback l E f).obj K.obj) ≫
      (integralComparisonDerivedSequenceScalar l E L ι X).map
        ((integralComparisonPullbackCounit l E f
          ((C.coefficient E).system Y) ((C.coefficient E).system X)
          ((C.coefficient E).roos X) ((C.coefficient E).pullback f)).app K.obj) ≫
      (integralComparisonSystemScalarPullback l E L ι f).hom.app
        (((C.coefficient E).system Y).reduction.obj K.obj) := by
  classical
  let W : Bool → Scheme.{u} := Bool.rec Y X
  obtain ⟨ME₀, _⟩ := CompletedOperations.normalizedCompletedOperationModels l E W (by
    intro a
    cases a
    · exact fun x ↦ isUnit_of_invertible (l : Y.residueField x)
    · exact fun x ↦ isUnit_of_invertible (l : X.residueField x))
  obtain ⟨ML₀, _⟩ := CompletedOperations.normalizedCompletedOperationModels l L W (by
    intro a
    cases a
    · exact fun x ↦ isUnit_of_invertible (l : Y.residueField x)
    · exact fun x ↦ isUnit_of_invertible (l : X.residueField x))
  let ME := scalarCounitModels l E (C.coefficient E) W ME₀
  let ML := scalarCounitModels l L (C.coefficient L) W ML₀
  obtain ⟨TE⟩ := (ScalarExtensionTower.realizationModels l E L ι W ME ML (by
    intro a
    cases a
    · exact fun x ↦ isUnit_of_invertible (l : Y.residueField x)
    · exact fun x ↦ isUnit_of_invertible (l : X.residueField x)) false).1
  obtain ⟨TL⟩ := (ScalarExtensionTower.realizationModels l L L
    (AlgHom.id ℚ_[l] L) W ML ML (by
      intro a
      cases a
      · exact fun x ↦ isUnit_of_invertible (l : Y.residueField x)
      · exact fun x ↦ isUnit_of_invertible (l : X.residueField x)) false).1
  obtain ⟨hF', _, h, _⟩ := ScalarExtensionTower.scalarExtensionTowerCoherence
    l E L ι W ME ML ((C.scalar E L ι).model X) ((C.scalar E L ι).model Y)
    TE TL f (scalarCounitPrimeUnit l X) (scalarCounitPrimeUnit l Y) K K
  simpa only [ME, ML, scalarCounitModels, W,
    ScalarExtensionTower.pullbackReduction, ScalarExtensionTower.scalarReduction,
    integralComparisonPullbackCounit, integralComparisonScalarCounit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Category.assoc] using h

end WeilConjectures
