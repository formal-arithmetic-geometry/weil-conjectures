/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteOpenExchangeFace

/-! Open mate after the transported open comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private theorem cancel_map_inverse {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) {W : D}
    {a : W ⟶ F.obj X} {b : W ⟶ F.obj Y} (h : b ≫ F.map e.inv = a) :
    a ≫ F.map e.hom = b := by
  rw [← h, Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The scalar realization preserves the derived open adjunction unit.
Source: blueprint operations proof (2), open coordinate unit square.
(blueprint: new-lem-sp-strict-finite-open-projection-open-unit).
Proof: conjugate the ordinary open adjunction by the scalar equivalences.
Naturality of its unit and the equivalence triangle identities give the ordinary
unit square. Apply the cochain functor and exact localization, then cancel the
exact-to-left-derived pullback comparisons. This gives the stated derived square.
The argument uses only units and triangles, so includes identity and empty opens. -/
theorem strictFiniteOpenProjectionOpenUnit (b : Base l E)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))))) :
    (comparisonFiniteRealization l E b U n).map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).ofNatIsoRight
          (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
            j).leftDerivedFunctorIsoMapDerivedCategory.symm).unit.app K) ≫
      (comparisonFinitePull l E b j n).hom.app
        ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) j).mapDerivedCategory.obj K) ≫
      (proEtaleConstantRingDerivedPullback (R l E n) j).map
        ((comparisonFiniteOpen l E b j n).hom.app K) =
      (comparisonLevelOpenAdjunction l E b j n).unit.app
        ((comparisonFiniteRealization l E b U n).obj K) := by
  have h := strict_finite_open_unit l E b j n K
  have hc := cancel_map_inverse (proEtaleConstantRingDerivedPullback (R l E n) j)
    ((comparisonFiniteOpen l E b j n).app K) h
  simp only [Category.assoc, Iso.app_hom,
    derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    leftDerivedUpperStarIsoMapDerivedCategory] at hc
  simpa only [Functor.id_obj, Functor.comp_obj] using hc

end AlgebraicGeometry.ProEtale.SpTowerShriek
