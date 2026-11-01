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
# The derived pullback of a constant sheaf placed in degree zero

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

/-- The derived pullback of the constant sheaf `Λ_Y` placed in degree zero, followed by the
identification `f^* Λ_Y ≅ Λ_X`, is
`AlgebraicGeometry.Etale.leftDerivedUpperStarSingleConstantSheafIso`. -/
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

end AlgebraicGeometry.Etale
