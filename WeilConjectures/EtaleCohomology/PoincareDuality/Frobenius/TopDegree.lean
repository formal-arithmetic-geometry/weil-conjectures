/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.UnitPairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-!
# The top and bottom degree cohomology of a proper connected scheme over a closed field

Let `a : X ⟶ Spec k` be proper and geometrically connected over an algebraically closed field,
with a Tate orientation of relative dimension `d`, and `Λ` a finite self-injective coefficient
ring. Then:

* `H^{2d}(X, Λ) ≅ Λ`
  (`AlgebraicGeometry.Etale.TateOrientation.nonempty_addEquiv_unitShift_two_mul`),
  through the bijective untwisted trace
  `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)` and `Λ(-d) ≅ Λ` over `k`;
* `H^0(X, Λ) ≅ Λ` (`AlgebraicGeometry.Etale.nonempty_addEquiv_unitShift_zero`);
* the Frobenius operator of an automorphism acts trivially on `H^0(X, Λ)`
  (`AlgebraicGeometry.Etale.frobeniusOperator_shiftWeilDatum_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

variable (Λ) in
/-- On a connected scheme, `H^0(X, Λ) = Hom(Λ_X, Λ_X[0])` is `Λ`. -/
theorem nonempty_addEquiv_unitShift_zero (X : Scheme.{u}) [ConnectedSpace X] :
    Nonempty ((𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(0 : ℤ)⟧) ≃+
      Λ) :=
  ⟨(AddEquiv.mk' ((Iso.refl _).homCongr
    ((shiftFunctorZero (DerivedCategoryModule Λ X) ℤ).app _)) fun f g ↦ by simp).trans
      (endUnitAddEquiv Λ X).symm⟩

/-- The Frobenius operator of an endomorphism `h` fixes the class `Λ_X ≅ Λ_X[0]`. -/
lemma frobeniusOperator_shiftWeilDatum_zero_shiftFunctorZero_inv {X : Scheme.{u}} (h : X ⟶ X) :
    frobeniusOperator h (shiftWeilDatum h (leftDerivedUpperStarUnitIso _ h).hom 0)
        ((shiftFunctorZero (DerivedCategoryModule Λ X) ℤ).inv.app
          (𝟙_ (DerivedCategoryModule Λ X))) =
      (shiftFunctorZero (DerivedCategoryModule Λ X) ℤ).inv.app
        (𝟙_ (DerivedCategoryModule Λ X)) := by
  rw [frobeniusOperator_apply, shiftWeilDatum, Functor.commShiftIso_zero,
    Functor.CommShift.isoZero_hom_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id,
    Category.id_comp]
  erw [← (shiftFunctorZero (DerivedCategoryModule Λ X) ℤ).inv.naturality]
  simp

/-- **The Frobenius acts trivially on `H^0`.** On a connected scheme, the Frobenius operator of
an endomorphism `h` is the identity on `H^0(X, Λ) = Hom(Λ_X, Λ_X[0])`. -/
lemma frobeniusOperator_shiftWeilDatum_zero {X : Scheme.{u}} [ConnectedSpace X] (h : X ⟶ X)
    (y : 𝟙_ (DerivedCategoryModule Λ X) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦(0 : ℤ)⟧) :
    frobeniusOperator h (shiftWeilDatum h (leftDerivedUpperStarUnitIso _ h).hom 0) y = y := by
  obtain ⟨c, hc⟩ := (bijective_smul_id_unit Λ X).2
    (y ≫ (shiftFunctorZero (DerivedCategoryModule Λ X) ℤ).hom.app _)
  have hy : y = c • (shiftFunctorZero (DerivedCategoryModule Λ X) ℤ).inv.app
      (𝟙_ (DerivedCategoryModule Λ X)) := by
    rw [← Category.id_comp ((shiftFunctorZero (DerivedCategoryModule Λ X) ℤ).inv.app _),
      ← Linear.smul_comp]
    beta_reduce at hc
    erw [hc]
    rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hy, map_smul, frobeniusOperator_shiftWeilDatum_zero_shiftFunctorZero_inv]

variable [Finite Λ] [Module.Injective Λ Λ] [HasTateTwist Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [HasInvertibleExponent Λ X] {d : ℕ}
  {a : X ⟶ Spec (.of k)} [IsProper a] [HasCompactification a] [GeometricallyConnected a]

/-- **`H^{2d}(X, Λ) ≅ Λ`.** For `X` proper and geometrically connected over an algebraically
closed field with a Tate orientation `γ`, the untwisted trace `H^{2d}(X, Λ) ⟶ Λ(-d)` is bijective
and `Λ(-d) ≅ Λ`. -/
theorem TateOrientation.nonempty_addEquiv_unitShift_two_mul (γ : TateOrientation Λ a d) :
    Nonempty ((𝟙_ (DerivedCategoryModule Λ X) ⟶
      (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧) ≃+ Λ) := by
  obtain ⟨e⟩ := nonempty_tateObject_iso_unit Λ k (-(d : ℤ))
  exact ⟨(AddEquiv.ofBijective _
    (TateOrientation.bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport a γ)).trans
      ((AddEquiv.mk' ((Iso.refl _).homCongr e) fun f g ↦ by simp).trans
        (endUnitAddEquiv Λ (Spec (.of k))).symm)⟩

end AlgebraicGeometry.Etale
