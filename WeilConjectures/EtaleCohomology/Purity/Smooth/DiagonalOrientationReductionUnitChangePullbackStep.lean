/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangePullbackZMod

/-!
# The derived pullback of the direct identification of the constant complex, unfolded

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

/-- The pullback of the direct identification `Λ_Y ≅ (Λ ⊗ ℤ)[0]`, unfolded. -/
lemma leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_comp_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
        (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit Y Λ).hom ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
        ((extendScalars Λ Y).obj Y.constantSheafInt) ≫
      (DerivedCategory.singleFunctor _ 0).map (upperStarExtendScalarsConstantSheafIntIso Λ f).hom =
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) Y).inv ≫
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map
        (extendScalarsConstantZModIso (Λ := Λ) Y (n := 0) (by simp)).inv) ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map
        (upperStarExtendScalarsConstantSheafIntIso Λ f).hom := by
  rw [constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_eq, Functor.map_comp,
    Category.assoc]

/-- The pullback of `Λ ≅ Λ ⊗ ℤ` placed in degree zero, after the unit of `D(Y_ét)`. -/
lemma leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp_map_extendScalarsConstantZModIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) Y).inv ≫
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map
        (extendScalarsConstantZModIso (Λ := Λ) Y (n := 0) (by simp)).inv) ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map (upperStarExtendScalarsConstantSheafIntIso Λ f).hom =
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) Y).inv ≫
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app (ModuleCat.of Λ Λ)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).inv := by
  rw [leftDerivedUpperStar_map_singleFunctor_map_extendScalarsConstantZModIso_inv_comp]

end AlgebraicGeometry.Etale
