/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Submission.WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Horizontal coherence of the canonical additive Roos comparison

Source: Stacks Tag 0941, lemma-derived-limit-is-ok, product-cone context, and the
agent-written coordinate calculation in the DAG proof
(blueprint: lem-pur-roos-comparison-horizontal-coherence).

The comparison is constructed directly by Mathlib's `mappingCocone.lift` on the fixed
`roosF` model, using the two mapped projections and the canonical product comparison.
No exactness or preservation of products is assumed for its definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe uA vA uB vB uD vD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasCountableProducts D]

private lemma comparison_fst (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.fst =
      F.map ((roosχ X p).hom ≫ biprod.fst) ≫ (roosProductComparison F X).f p := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

private lemma comparison_snd (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosAdditiveComparison F X).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj X) p).hom ≫ biprod.snd =
      F.map ((roosχ X p).hom ≫ biprod.snd) ≫
        (roosProductComparison F X).f (p + 1) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosAdditiveComparison_coordinates]
    simp [Functor.map_comp]

private lemma productComparison_natural (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (h : X ⟶ Y) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosPmap h) ≫
        roosProductComparison F Y =
      roosProductComparison F X ≫ roosPmap ((roosTowerAction F).map h) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply Pi.hom_ext
    intro n
    change (_ ≫ roosProductComparison F Y) ≫ Pi.π (fun n : ℕ ↦
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Y.asFunctor.obj (op n))) n = _
    simp only [Category.assoc, roosProductComparison, piComparison_comp_π, roosPmap,
      Pi.map_π, ← Functor.map_comp]
    change _ = piComparison (F.mapHomologicalComplex (ComplexShape.up ℤ)) _ ≫
      Pi.π (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (X.asFunctor.obj (op n))) n ≫ _
    rw [piComparison_comp_π_assoc, Functor.map_comp]
    rfl

private lemma roos_map_fst {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (h : X ⟶ Y) (p : ℤ) :
    (roosF.map h).f (p + 1) ≫ (roosχ Y p).hom ≫ biprod.fst =
      (roosχ X p).hom ≫ biprod.fst ≫ (roosPmap h).f p := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosF_map_χ]
    simp

private lemma roos_map_snd {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (h : X ⟶ Y) (p : ℤ) :
    (roosF.map h).f (p + 1) ≫ (roosχ Y p).hom ≫ biprod.snd =
      (roosχ X p).hom ≫ biprod.snd ≫ (roosPmap h).f (p + 1) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    rw [← Category.assoc, roosF_map_χ]
    simp

/-- Naturality is equality of strict cochain maps.
Source: Stacks Tag 0941 (blueprint: lem-pur-roos-comparison-horizontal-coherence).
Proof: DAG step 4. Postcompose with each product projection of each biproduct
coordinate. Both sides are the functor image of the same coordinate of the tower
map, by functoriality. Product and biproduct extensionality give equality. -/
theorem roosAdditiveComparison_natural (F : A ⥤ B) [F.Additive]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (h : X ⟶ Y) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosF.map h) ≫
        roosAdditiveComparison F Y =
      roosAdditiveComparison F X ≫ roosF.map ((roosTowerAction F).map h) := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    ext k
    obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (roosF.map h) ≫
      roosAdditiveComparison F Y).f (p + 1) =
        (roosAdditiveComparison F X ≫ roosF.map ((roosTowerAction F).map h)).f (p + 1)
    apply (cancel_mono (roosχ ((roosTowerAction F).obj Y) p).hom).1
    simp only [HomologicalComplex.comp_f]
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [comparison_fst F Y p, roos_map_fst ((roosTowerAction F).map h) p]
      erw [reassoc_of% comparison_fst F X p]
      simp only [Functor.mapHomologicalComplex_map_f]
      rw [← Category.assoc, ← F.map_comp, roos_map_fst]
      have hp := congrArg (fun f ↦ f.f p) (productComparison_natural F h)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp
      simp only [F.map_comp, Category.assoc]
      rw [hp]
    · simp only [Category.assoc]
      erw [comparison_snd F Y p, roos_map_snd ((roosTowerAction F).map h) p]
      erw [reassoc_of% comparison_snd F X p]
      simp only [Functor.mapHomologicalComplex_map_f]
      rw [← Category.assoc, ← F.map_comp, roos_map_snd]
      have hp := congrArg (fun f ↦ f.f (p + 1)) (productComparison_natural F h)
      dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp
      simp only [F.map_comp, Category.assoc]
      rw [hp]

end CategoryTheory
