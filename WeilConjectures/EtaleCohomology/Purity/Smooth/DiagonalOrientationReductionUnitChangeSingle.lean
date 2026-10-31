/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangeEq

/-!
# The change of coefficients of the constant complexes through the unit sheaves

We write the change of coefficients `Λ_X ⟶ Res Λ'_X` of the constant complexes
(`AlgebraicGeometry.Etale.constantComplexChangeMap`) through the identifications of the units of
the derived categories with the unit sheaves placed in degree zero
(`AlgebraicGeometry.Etale.constantComplexChangeMap_eq`). This lemma is alone in its file, its
kernel check being expensive.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- The change of coefficients of the constant complexes
(`AlgebraicGeometry.Etale.constantComplexChangeMap`) through the identifications of the units
of the derived categories with the unit sheaves placed in degree zero. -/
lemma constantComplexChangeMap_eq [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] :
    constantComplexChangeMap ρ X =
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).inv ≫
            (extendScalarsChangeMap ρ X).app X.constantSheafInt ≫
            (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
              (extendScalarsConstantZModIso (Λ := Λ') X (n := 0) (by simp)).hom) ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          (𝟙_ _) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ') X).hom := by
  rw [constantComplexChangeMap_eq_ofUnit, constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom,
    constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_inv]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (map_extendScalarsConstantZModIso_hom_comp_mapDerivedCategorySingleFunctor_inv_app
    ρ X)]

end AlgebraicGeometry.Etale
