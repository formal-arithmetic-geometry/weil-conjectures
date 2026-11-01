/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangeConstant
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-!
# Unfolding the identifications of the constant complexes

The two identifications `Λ_X ≅ (Λ ⊗ ℤ)[0]` (pulled back from `Spec ℤ[1/n]`, and the direct one),
the derived pullback of the constant complex, and the pullback of `Λ ⊗ ℤ ≅ Λ` of constant sheaves.

This is one step of the proof of
`constantComplexIsoSingleFunctorExtendScalarsInt_eq_constantComplexIsoOfUnit`;
the steps are kept in separate files because each one is expensive for the kernel (the statements
involve the definitional identification of the unit of the étale sheaves with the constant sheaf).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The identification `Λ ⊗ ℤ ≅ Λ` of constant sheaves is compatible with the pullback along
`f : X ⟶ Y`. -/
lemma upperStar_map_extendScalarsConstantZModIso_inv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*[ModuleCat.{u + 1} Λ].map
        (extendScalarsConstantZModIso (Λ := Λ) Y (n := 0) (by simp)).inv ≫
      (upperStarExtendScalarsConstantSheafIntIso Λ f).hom =
    (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app (ModuleCat.of Λ Λ) ≫
      (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).inv := by
  rw [← cancel_mono (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    upperStarExtendScalarsConstantSheafIntIso_hom_comp, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes is the unit comparison
`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`. -/
lemma leftDerivedUpperStarConstantComplexIso_hom_eq_unitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftDerivedUpperStarConstantComplexIso Λ f).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom :=
  leftDerivedUpperStarOplaxMonoidal_η _ f

/-- The identification `Λ_X ≅ (Λ ⊗ ℤ)[0]` is pulled back from `Spec ℤ[1/n]`. -/
lemma constantComplexIsoSingleFunctorExtendScalarsInt_hom_eq (X : Scheme.{u})
    [HasInvertibleExponent Λ X] :
    (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom =
      (leftDerivedUpperStarConstantComplexIso Λ (toInvertibleExponentBase (Λ := Λ) X)).inv ≫
        ((toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
          (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit
            (invertibleExponentBase.{u} Λ) Λ).hom ≫
        (singleFunctorCompLeftDerivedUpperStarIso _ (toInvertibleExponentBase (Λ := Λ) X)).hom.app
          ((extendScalars Λ (invertibleExponentBase.{u} Λ)).obj
            (invertibleExponentBase.{u} Λ).constantSheafInt) ≫
        (DerivedCategory.singleFunctor _ 0).map
          (upperStarExtendScalarsConstantSheafIntIso Λ (toInvertibleExponentBase (Λ := Λ) X)).hom :=
  rfl

/-- The direct identification `Λ_X ≅ (Λ ⊗ ℤ)[0]` is the unit of `D(X_ét)` followed by
`Λ ≅ Λ ⊗ ℤ` placed in degree zero. -/
lemma constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_eq (X : Scheme.{u}) :
    (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ).hom =
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map
          (extendScalarsConstantZModIso X (n := 0) (by simp)).inv :=
  rfl

end AlgebraicGeometry.Etale
