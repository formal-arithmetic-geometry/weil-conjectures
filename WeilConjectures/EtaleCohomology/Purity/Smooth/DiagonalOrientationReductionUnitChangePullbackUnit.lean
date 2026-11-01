/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangePullbackUnitAux

/-!
# The derived pullback of the unit placed in degree zero

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
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv :=
  leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp_singleFunctor_map_unit Λ f

end AlgebraicGeometry.Etale
