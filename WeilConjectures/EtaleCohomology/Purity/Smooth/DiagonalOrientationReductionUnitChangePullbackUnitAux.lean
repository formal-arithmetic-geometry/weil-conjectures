/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangePullbackSingle

/-!
# The derived pullback of the unit placed in degree zero, at the unit of the coefficients

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

/-- The unit of `D(Y_ét)` placed in degree zero, pulled back along `f : X ⟶ Y` (stated at the
unit `𝟙_` of the coefficients). -/
lemma leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp_singleFunctor_map_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((f)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctor.map
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) Y).inv ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (𝟙_ _)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app (𝟙_ _)) =
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom ≫
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv := by
  rw [singleFunctorCompLeftDerivedUpperStarIso_hom_app_comp]
  exact leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp _ f

end AlgebraicGeometry.Etale
