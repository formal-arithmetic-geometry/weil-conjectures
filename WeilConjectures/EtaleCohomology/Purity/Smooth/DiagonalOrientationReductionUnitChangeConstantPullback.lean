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
# test
-/

@[expose] public section

set_option profiler true
set_option profiler.threshold 1000

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable (Λ : Type (u + 1)) [CommRing Λ]

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

lemma singleFunctorCompLeftDerivedUpperStarIso_hom_app_comp {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (𝟙_ _)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app (𝟙_ _)) =
    (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) f (𝟙_ _)).hom := by
  simp only [singleFunctorCompLeftDerivedUpperStarIso,
    Functor.singleFunctorCompLeftDerivedFunctorIso, leftDerivedUpperStarSingleConstantSheafIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
    leftDerivedUpperStarIsoMapDerivedCategory]

/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes is the unit comparison
`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`. -/
lemma leftDerivedUpperStarConstantComplexIso_hom_eq_unitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (leftDerivedUpperStarConstantComplexIso Λ f).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom :=
  leftDerivedUpperStarOplaxMonoidal_η _ f

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

lemma constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_eq (X : Scheme.{u}) :
    (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ).hom =
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map
          (extendScalarsConstantZModIso X (n := 0) (by simp)).inv :=
  rfl


/-- The identifications `Λ ⊗ ℤ ≅ Λ` placed in degree zero are compatible with the derived pullback
along `f : X ⟶ Y`. -/
lemma leftDerivedUpperStar_map_singleFunctor_map_extendScalarsConstantZModIso_inv_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map
        (extendScalarsConstantZModIso (Λ := Λ) Y (n := 0) (by simp)).inv) ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map (upperStarExtendScalarsConstantSheafIntIso Λ f).hom =
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app (ModuleCat.of Λ Λ)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).inv := by
  have hσ := (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.naturality
    (extendScalarsConstantZModIso (Λ := Λ) Y (n := 0) (by simp)).inv
  simp only [Functor.comp_map] at hσ
  rw [reassoc_of% hσ, ← Functor.map_comp, upperStar_map_extendScalarsConstantZModIso_inv_comp,
    Functor.map_comp]

/-- The unit of `D(Y_ét)` placed in degree zero, pulled back along `f : X ⟶ Y`. -/
lemma leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp_singleFunctor_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) Y).inv ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app (ModuleCat.of Λ Λ)) =
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom ≫
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv := by
  rw [singleFunctorCompLeftDerivedUpperStarIso_hom_app_comp]
  exact leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp _ f


lemma constantComplexIsoSingleFunctorExtendScalarsInt_eq_ofUnit' (X : Scheme.{u})
    [HasInvertibleExponent Λ X] :
    constantComplexIsoSingleFunctorExtendScalarsInt X Λ =
      constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ := by
  ext
  rw [constantComplexIsoSingleFunctorExtendScalarsInt_hom_eq,
    constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_eq,
    constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_eq, Functor.map_comp, Category.assoc,
    leftDerivedUpperStar_map_singleFunctor_map_extendScalarsConstantZModIso_inv_comp,
    reassoc_of% leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp_singleFunctor_map,
    ← leftDerivedUpperStarConstantComplexIso_hom_eq_unitIso, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Etale
