/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChange

/-!
# The change of coefficients of the constant complexes through the unit sheaves

We relate the change of coefficients `Λ_X ⟶ Res Λ'_X` of the constant complexes
(`AlgebraicGeometry.Etale.constantComplexChangeMap`) to the direct identifications
`Λ_X ≅ (Λ ⊗ ℤ)[0]` (`AlgebraicGeometry.Etale.constantComplexChangeMap_eq_ofUnit`).

The proof is split into several lemmas, as the kernel checks each of them only slowly.
-/

@[expose] public section

universe u


open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- The naturality of `Res(-)[0] ≅ (Res -)[0]` with respect to `Λ' ⊗ ℤ ≅ Λ'`, at the unit. -/
lemma map_extendScalarsConstantZModIso_hom_comp_mapDerivedCategorySingleFunctor_inv_app :
    (DerivedCategory.singleFunctor _ 0).map ((Sheaf.restrictScalars X.smallEtaleTopology ρ).map
      (extendScalarsConstantZModIso (Λ := Λ') X (n := 0) (by simp)).hom) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
        (𝟙_ _) =
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
        _ ≫ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          ((DerivedCategory.singleFunctor _ 0).map
            (extendScalarsConstantZModIso (Λ := Λ') X (n := 0) (by simp)).hom) :=
  ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor
    0).inv.naturality (extendScalarsConstantZModIso (Λ := Λ') X (n := 0) (by simp)).hom

/-- The change of coefficients of the constant complexes through the direct identifications
`Λ_X ≅ (Λ ⊗ ℤ)[0]`. -/
lemma constantComplexChangeMap_eq_ofUnit [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] :
    constantComplexChangeMap ρ X =
      (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ).hom ≫
        (DerivedCategory.singleFunctor _ 0).map ((extendScalarsChangeMap ρ X).app _) ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ').inv := by
  rw [constantComplexChangeMap, constantComplexIsoSingleFunctorExtendScalarsInt_eq_ofUnit,
    constantComplexIsoSingleFunctorExtendScalarsInt_eq_ofUnit, singleFunctorRestrictScalarsIso_hom]

omit [CommRing Λ'] in
/-- The direct identification `Λ_X ≅ (Λ ⊗ ℤ)[0]`. -/
lemma constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom [HasInvertibleExponent Λ X] :
    (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ).hom =
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map
          (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).inv :=
  rfl

omit [CommRing Λ'] in
/-- The direct identification `Λ_X ≅ (Λ ⊗ ℤ)[0]`. -/
lemma constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_inv [HasInvertibleExponent Λ X] :
    (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ).inv =
      (DerivedCategory.singleFunctor _ 0).map
          (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).hom ≫
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).hom :=
  rfl

end AlgebraicGeometry.Etale
