/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Mathlib.CategoryTheory.GuitartExact.KanExtension

/-!
# Existence of pointwise left derived functors via derivability structures

In this file, we show how a left derivability structure can be used in
order to construct (pointwise) left derived functors.
Let `Φ` be a left derivability structure from `W₁ : MorphismProperty C₁`
to `W₂ : MorphismProperty C₂`. Let `F : C₂ ⥤ H` be a functor.
Then, the lemma `hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure`
says that `F` has a pointwise left derived functor with respect to `W₂`
if and only if `Φ.functor ⋙ F` has a pointwise left derived functor
with respect to `W₁`.

In particular, if `Φ.functor ⋙ F` inverts `W₁`, it follows that the
left derived functor of `F` with respect to `W₂` exists.

This file was obtained by dualizing
`Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean`;
the two files should be kept in sync.

In mathlib, this file would be
`Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseLeftDerived.lean`.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits Category Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₄} D₁] [Category.{v₅} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (F : C₂ ⥤ H) (F₁ : D₁ ⥤ H) (α₁ : L₁ ⋙ F₁ ⟶ Φ.functor ⋙ F)
  (F₂ : D₂ ⥤ H) (α₂ : L₂ ⋙ F₂ ⟶ F)
  [F₁.IsLeftDerivedFunctor α₁ W₁]

/-- If `Φ` is a localizer morphism from `W₁ : MorphismProperty C₁` to
`W₂ : MorphismProperty C₂`, if `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, if `F : C₂ ⥤ H` is a functor,
if `F₁ : D₁ ⥤ H` is a left derived functor of `Φ.functor ⋙ F`,
and if `F₂ : D₂ ⥤ H` is a functor equipped with a
natural transformation `α₂ : L₂ ⋙ F₂ ⟶ F`, this is the canonical
morphism `Φ.localizedFunctor L₁ L₂ ⋙ F₂ ⟶ F₁`. -/
noncomputable def leftDerivedFunctorComparison :
    Φ.localizedFunctor L₁ L₂ ⋙ F₂ ⟶ F₁ :=
  F₁.leftDerivedLift α₁ W₁ (Φ.localizedFunctor L₁ L₂ ⋙ F₂)
    ((Functor.associator _ _ _).inv ≫
      whiskerRight ((Φ.catCommSq L₁ L₂).iso).inv F₂ ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft _ α₂)

@[reassoc]
lemma leftDerivedFunctorComparison_fac :
    whiskerLeft _ (Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) ≫ α₁ =
      ((Functor.associator _ _ _).inv ≫
        whiskerRight ((Φ.catCommSq L₁ L₂).iso).inv F₂ ≫
        (Functor.associator _ _ _).hom) ≫ whiskerLeft Φ.functor α₂ := by
  dsimp only [leftDerivedFunctorComparison]
  rw [Functor.leftDerived_fac]
  simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma leftDerivedFunctorComparison_fac_app (X : C₁) :
    (Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X) ≫ α₁.app X =
      F₂.map (((Φ.catCommSq L₁ L₂).iso).inv.app X) ≫ α₂.app (Φ.functor.obj X) := by
  simpa using congr_app (Φ.leftDerivedFunctorComparison_fac L₁ L₂ F F₁ α₁ F₂ α₂) X

variable [Φ.IsLeftDerivabilityStructure]

lemma hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctorAt W₁ X ↔
      F.HasPointwiseLeftDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  let e : W₂.Q.obj _ ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj _ := ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseLeftDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseLeftDerivedFunctorAt_iff W₁.Q W₁ X,
    TwoSquare.hasPointwiseRightKanExtensionAt_iff ((Φ.catCommSq W₁.Q W₂.Q).iso).inv,
    Functor.hasPointwiseRightKanExtensionAt_iff_of_iso W₂.Q F e]

lemma hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure :
    F.HasPointwiseLeftDerivedFunctor W₂ ↔
      ((Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctor W₁) := by
  constructor
  · intro hF X₁
    rw [hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure]
    apply hF
  · intro hF X₂
    have L : Φ.LeftResolution X₂ := Classical.arbitrary _
    simpa only [hasPointwiseLeftDerivedFunctorAt_iff_of_isLeftDerivabilityStructure,
      F.hasPointwiseLeftDerivedFunctorAt_iff_of_mem W₂ L.w L.hw] using hF L.X₁

section

variable [(Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctor W₁]
  [F₂.IsLeftDerivedFunctor α₂ W₂]

instance : IsIso (Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂) := by
  have : F.HasPointwiseLeftDerivedFunctor W₂ := by
    rw [Φ.hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure]
    infer_instance
  dsimp only [leftDerivedFunctorComparison]
  rw [← isLeftDerivedFunctor_iff_isIso_leftDerivedLift,
    isLeftDerivedFunctor_iff_isRightKanExtension]
  exact ((F₂.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor α₂ W₂).compTwoSquare
    ((Φ.catCommSq L₁ L₂).iso).inv).isRightKanExtension

set_option backward.isDefEq.respectTransparency false in
lemma isIso_iff_of_isLeftDerivabilityStructure (X : C₁) :
    IsIso (α₁.app X) ↔ IsIso (α₂.app (Φ.functor.obj X)) := by
  rw [← isIso_comp_left_iff
    ((Φ.leftDerivedFunctorComparison L₁ L₂ F F₁ α₁ F₂ α₂).app (L₁.obj X)) (α₁.app X),
    leftDerivedFunctorComparison_fac_app, isIso_comp_left_iff]

end

end LocalizerMorphism

end CategoryTheory
