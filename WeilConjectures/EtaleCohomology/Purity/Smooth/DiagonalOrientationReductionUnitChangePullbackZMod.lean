/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChangePullbackSheaf

/-!
# The derived pullback of `Λ ⊗ ℤ ≅ Λ` placed in degree zero

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

end AlgebraicGeometry.Etale
