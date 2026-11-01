/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangePullbackStep
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangePullbackStepUnit

/-!
# The identification of the constant complex is compatible with pullbacks

The identification `Λ_X ≅ (Λ ⊗ ℤ)[0]` used for the Kummer classes, which is pulled back from
`Spec ℤ[1/n]` (`AlgebraicGeometry.Etale.constantComplexIsoSingleFunctorExtendScalarsInt`), is the
direct one (`AlgebraicGeometry.Etale.constantComplexIsoSingleFunctorExtendScalarsIntOfUnit`),
because the latter is compatible with derived pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The direct identification `Λ_Y ≅ (Λ ⊗ ℤ)[0]` is compatible with the derived pullback. -/
lemma leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
        (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit Y Λ).hom ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
        ((extendScalars Λ Y).obj Y.constantSheafInt) ≫
      (DerivedCategory.singleFunctor _ 0).map (upperStarExtendScalarsConstantSheafIntIso Λ f).hom =
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom ≫
      (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ).hom :=
  (leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_comp_eq Λ
      f).trans
    ((leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp_map_extendScalarsConstantZModIso_inv
      Λ f).trans (leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp_constantSheaf_comp Λ f))

/-- **The identification `Λ_X ≅ (Λ ⊗ ℤ)[0]` pulled back from `Spec ℤ[1/n]` is the direct one**
(blueprint `det-sp-purity-coefficient-change`). -/
lemma constantComplexIsoSingleFunctorExtendScalarsInt_eq_constantComplexIsoOfUnit
    (X : Scheme.{u})
    [HasInvertibleExponent Λ X] :
    constantComplexIsoSingleFunctorExtendScalarsInt X Λ =
      constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X Λ := by
  ext
  rw [constantComplexIsoSingleFunctorExtendScalarsInt_hom_eq,
    leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsIntOfUnit_hom_comp,
    ← leftDerivedUpperStarConstantComplexIso_hom_eq_unitIso, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Etale
