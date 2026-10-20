/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G5
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Invertibility of the diagonal source comparison

Source: blueprint lem-amb-p1-diagonal-integrals, standard-chart Cartier calculation;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport


private theorem isIso_pasted_units
    {C D : Type*} [Category C] [Category D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ C} {R₂ : C ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₁ ⋙ L₂ ≅ 𝟭 C)
    {X : C} {Y : D} {Z : C} (e₁ : L₁.obj X ≅ Y) (e₂ : L₂.obj Y ≅ Z) :
    IsIso ((adj₁.unit.app X ≫ R₁.map e₁.hom) ≫
      R₁.map (adj₂.unit.app Y ≫ R₂.map e₂.hom)) := by
  have : (L₁ ⋙ L₂).Full := Functor.Full.of_iso e.symm
  have : (L₁ ⋙ L₂).Faithful := Functor.Faithful.of_iso e.symm
  have he : (adj₁.unit.app X ≫ R₁.map e₁.hom) ≫
      R₁.map (adj₂.unit.app Y ≫ R₂.map e₂.hom) =
      (adj₁.comp adj₂).unit.app X ≫
        (R₂ ⋙ R₁).map (L₂.map e₁.hom ≫ e₂.hom) := by
    simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [← R₁.map_comp_assoc, ← adj₂.unit_naturality, R₁.map_comp]
    simp only [Category.assoc]
  rw [he]
  infer_instance

attribute [local irreducible] projectiveLineDiagonalAlpha ordinaryFiniteUnitPullback
  derivedUpperStarLowerStarAdjunction

/-- The canonical source comparison for the diagonal is an isomorphism over every base.
Source: blueprint lem-amb-p1-diagonal-integrals, derived-composition identification alpha.
(blueprint: lem-sp-finite-p1-diagonal-alpha)

Proof: each projection composed with the diagonal is identity. The corresponding
composite inverse-image functor is therefore naturally isomorphic to identity,
so its adjunction unit is invertible. Expand the two constant-object units in alpha.
Naturality of the second unit rewrites their composite as the composite adjunction
unit followed by direct image of the two constant-object comparison isomorphisms.
Every factor is invertible. No compatibility choice or Noetherian hypothesis is needed. -/
theorem isIso_projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    IsIso (C := DerivedCategoryModule A (ProjectiveLine S))
      (projectiveLineDiagonalAlpha A S a) := by
  let p := projectiveLineDiagonalProjection S a
  let i := pullback.diagonal (ProjectiveLine S ↘ S)
  have hi : i ≫ p = 𝟙 (ProjectiveLine S) := by
    cases a <;> simp only [i, p, projectiveLineDiagonalProjection,
      pullback.diagonal_fst, pullback.diagonal_snd]
  let eId : (upperStar (ModuleCat.{u + 1} A) (𝟙 (ProjectiveLine S))).leftDerivedFunctor ≅
      𝟭 (DerivedCategoryModule A (ProjectiveLine S)) :=
    Functor.leftDerivedFunctorNatIso _
        (upperStarId (ModuleCat.{u + 1} A) (ProjectiveLine S)) ≪≫
      (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _
  let e := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i p
    (𝟙 (ProjectiveLine S)) hi.symm).symm ≪≫ eId
  unfold projectiveLineDiagonalAlpha supportedDerivedUnit
  exact isIso_pasted_units
    (L₁ := (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor)
    (R₁ := (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor)
    (L₂ := (upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor)
    (R₂ := (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor)
    (X := ordinaryFiniteUnit A (ProjectiveLine S))
    (Y := ordinaryFiniteUnit A
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    (Z := ordinaryFiniteUnit A (ProjectiveLine S))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i) e
    (ordinaryFiniteUnitPullback A p) (ordinaryFiniteUnitPullback A i)

end AlgebraicGeometry.Etale
