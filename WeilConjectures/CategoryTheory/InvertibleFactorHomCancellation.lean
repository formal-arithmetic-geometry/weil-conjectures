/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Internal-Hom cancellation by an invertible tensor factor

Source: Stacks Project, Categories, Tags 0FFM and 0GWJ, and their evaluation-transpose
consequence (blueprint: lem-sf-invertible-factor-hom-cancellation).

Mathlib uses left evaluation `X ⊗ [X,Y] ⟶ Y`. The right evaluation in the node is
its composite with the symmetry `[X,Y] ⊗ X ⟶ X ⊗ [X,Y]`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C]

/-- Simultaneous tensoring in both variables of internal Hom, defined by transposing
right evaluation tensored with the identity of `J`. No inverse-factor data is used.
Source: Stacks Project, Categories, Tag 0GWJ
(blueprint: lem-sf-invertible-factor-hom-cancellation). -/
noncomputable def ihomTensorBoth (X Y J : C) :
    (ihom X).obj Y ⟶ (ihom (X ⊗ J)).obj (Y ⊗ J) :=
  curry ((β_ (X ⊗ J) ((ihom X).obj Y)).hom ≫
    (α_ ((ihom X).obj Y) X J).inv ≫
    ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J)

/-- The two evaluation-normalized internal-Hom isomorphisms for an invertible factor.
Source: Stacks Project, Categories, Tags 0FFM and 0GWJ, agent consequence
(blueprint: lem-sf-invertible-factor-hom-cancellation).

Proof plan: (1) The specified inverse-factor isomorphisms and the associators and
right unitors give natural isomorphisms between the composites of tensoring by `J`
and by `I` and the identity. (2) The quasi-inverse Hom-bijection lemma, implemented
by `Equivalence.mk` and `fullyFaithfulFunctor.map_bijective`, makes tensoring by `J`
fully faithful and essentially surjective; no triangle condition on `a,b` is needed.
(3) Define the maps by the displayed evaluation transposes, using symmetry to
translate between left and right evaluation. (4--5) The existing theorem
`isIso_ihomTensorToIhom` proves invertibility of the first comparison by testing on
objects tensored with `J`, then transporting to arbitrary objects. (6) Uncurrying
postcomposition by `ihomTensorBoth` is tensoring an uncurried map by `J`, up to an
associator. Full faithfulness therefore gives bijectivity on all test-object Hom
sets and Yoneda gives invertibility. (7) Uncurry the naturality equations in `X,Y`:
both sides are evaluation composed with the indicated maps and tensored with `J`;
braiding naturality identifies the permutations. (8) Uncurry factor compatibility:
braiding naturality proves the first identity, and cancellation of the factor
isomorphism with its inverse proves the second. (9) Compose the evaluation and
naturality identities with the inverse maps to obtain inverse normalization and
naturality. The inverse of `s` is the canonical cancellation isomorphism.
-/
theorem invertibleFactorHomCancellation (J I : C)
    (a : J ⊗ I ≅ 𝟙_ C) (b : I ⊗ J ≅ 𝟙_ C) :
    ∃ (t : ∀ X Y : C, (ihom X).obj Y ⊗ J ≅ (ihom X).obj (Y ⊗ J))
      (s : ∀ X Y : C, (ihom X).obj Y ≅ (ihom (X ⊗ J)).obj (Y ⊗ J)),
      (∀ X Y : C, (t X Y).hom = ihomTensorToIhom X Y J ∧
        (s X Y).hom = ihomTensorBoth X Y J) ∧
      (∀ X Y : C,
        (t X Y).hom ▷ X ≫ (β_ ((ihom X).obj (Y ⊗ J)) X).hom ≫
            (ihom.ev X).app (Y ⊗ J) =
          (α_ ((ihom X).obj Y) J X).hom ≫
            (ihom X).obj Y ◁ (β_ J X).hom ≫
            (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J ∧
        (s X Y).hom ▷ (X ⊗ J) ≫
            (β_ ((ihom (X ⊗ J)).obj (Y ⊗ J)) (X ⊗ J)).hom ≫
            (ihom.ev (X ⊗ J)).app (Y ⊗ J) =
          (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J ∧
        (t X Y).inv ▷ X ≫ (α_ ((ihom X).obj Y) J X).hom ≫
            (ihom X).obj Y ◁ (β_ J X).hom ≫
            (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J =
          (β_ ((ihom X).obj (Y ⊗ J)) X).hom ≫ (ihom.ev X).app (Y ⊗ J) ∧
        (s X Y).inv ▷ (X ⊗ J) ≫ (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J =
          (β_ ((ihom (X ⊗ J)).obj (Y ⊗ J)) (X ⊗ J)).hom ≫
            (ihom.ev (X ⊗ J)).app (Y ⊗ J)) ∧
      (∀ (X X' Y Y' : C) (f : X' ⟶ X) (g : Y ⟶ Y'),
        ((pre f).app Y ≫ (ihom X').map g) ▷ J ≫ (t X' Y').hom =
          (t X Y).hom ≫ (pre f).app (Y ⊗ J) ≫ (ihom X').map (g ▷ J) ∧
        ((pre f).app Y ≫ (ihom X').map g) ≫ (s X' Y').hom =
          (s X Y).hom ≫ (pre (f ▷ J)).app (Y ⊗ J) ≫
            (ihom (X' ⊗ J)).map (g ▷ J) ∧
        ((pre f).app (Y ⊗ J) ≫ (ihom X').map (g ▷ J)) ≫ (t X' Y').inv =
          (t X Y).inv ≫ ((pre f).app Y ≫ (ihom X').map g) ▷ J ∧
        ((pre (f ▷ J)).app (Y ⊗ J) ≫ (ihom (X' ⊗ J)).map (g ▷ J)) ≫
            (s X' Y').inv =
          (s X Y).inv ≫ (pre f).app Y ≫ (ihom X').map g) ∧
      (∀ (X Y J' : C) (z : J ≅ J'),
        (ihom X).obj Y ◁ z.hom ≫ ihomTensorToIhom X Y J' =
          (t X Y).hom ≫ (ihom X).map (Y ◁ z.hom) ∧
        ihomTensorBoth X Y J' =
          (s X Y).hom ≫ (pre (X ◁ z.inv)).app (Y ⊗ J) ≫
            (ihom (X ⊗ J')).map (Y ◁ z.hom)) := by
  -- Use the right evaluation convention while keeping Mathlib's closed structure.
  let ru {X Y Z : C} (f : Z ⟶ (ihom X).obj Y) : Z ⊗ X ⟶ Y :=
    (β_ Z X).hom ≫ uncurry f
  have ru_inj {X Y Z : C} {f g : Z ⟶ (ihom X).obj Y} (h : ru f = ru g) : f = g :=
    uncurry_injective ((cancel_epi (β_ Z X).hom).1 h)
  have ru_left {X Y Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ (ihom X).obj Y) :
      ru (f ≫ g) = f ▷ X ≫ ru g := by
    dsimp only [ru]
    rw [uncurry_natural_left, ← BraidedCategory.braiding_naturality_left_assoc]
  have ru_right {X Y Y' Z : C} (f : Z ⟶ (ihom X).obj Y) (g : Y ⟶ Y') :
      ru (f ≫ (ihom X).map g) = ru f ≫ g := by
    simp only [ru, uncurry_natural_right, Category.assoc]
  have ru_pre {X X' Y Z : C} (f : Z ⟶ (ihom X).obj Y) (g : X' ⟶ X) :
      ru (f ≫ (pre g).app Y) = Z ◁ g ≫ ru f := by
    dsimp only [ru]
    rw [uncurry_pre_app, ← BraidedCategory.braiding_naturality_right_assoc]
  have ru_pair {X X' Y Y' Z : C} (f : Z ⟶ (ihom X).obj Y)
      (g : X' ⟶ X) (h : Y ⟶ Y') :
      ru (f ≫ (pre g).app Y ≫ (ihom X').map h) = Z ◁ g ≫ ru f ≫ h := by
    rw [← Category.assoc, ru_right, ru_pre, Category.assoc]
  have ru_pre0 {X X' Y : C} (f : X' ⟶ X) :
      ru ((pre f).app Y) = (ihom X).obj Y ◁ f ≫
        ru (𝟙 ((ihom X).obj Y)) := by
    simpa only [Category.id_comp] using ru_pre (𝟙 ((ihom X).obj Y)) f
  have ru_id (X Y : C) : ru (𝟙 ((ihom X).obj Y)) =
      (β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y := by
    simp only [ru, uncurry_id_eq_ev]
  have ru_s {X Y Z : C} (K : C) (f : Z ⟶ (ihom X).obj Y) :
      ru (f ≫ ihomTensorBoth X Y K) = (α_ Z X K).inv ≫ (ru f) ▷ K := by
    dsimp only [ru]
    rw [uncurry_natural_left, ihomTensorBoth, uncurry_curry,
      ← BraidedCategory.braiding_naturality_left_assoc, SymmetricCategory.symmetry_assoc,
      associator_inv_naturality_left_assoc]
    rw [← comp_whiskerRight, BraidedCategory.braiding_naturality_left_assoc,
      ← uncurry_eq]
  have ru_t (X Y K : C) :
      ru (ihomTensorToIhom X Y K) =
        (α_ ((ihom X).obj Y) K X).hom ≫
          (ihom X).obj Y ◁ (β_ K X).hom ≫
          (α_ ((ihom X).obj Y) X K).inv ≫
          (ru (𝟙 ((ihom X).obj Y))) ▷ K := by
    simp only [ru, ihomTensorToIhom, uncurry_curry, uncurry_id_eq_ev,
      BraidedCategory.braiding_tensor_left_hom, Category.assoc, Iso.hom_inv_id_assoc,
      comp_whiskerRight]
  -- Right uncurrying identifies this Yoneda map with tensoring a morphism by J.
  have s_iso (X Y : C) : IsIso (ihomTensorBoth X Y J) := by
    let E := tensorRightEquivalenceOfTensorIso a b
    refine isIso_of_yoneda_map_bijective _ (fun Z ↦ ⟨?_, ?_⟩)
    · intro f g h
      apply ru_inj
      apply whiskerRight_injective_of_tensorIso a
      apply (cancel_epi (α_ Z X J).inv).1
      rw [← ru_s J f, ← ru_s J g]
      exact congrArg ru h
    · intro g
      let q : Z ⊗ X ⟶ Y := E.functor.preimage ((α_ Z X J).hom ≫ ru g)
      have hq : q ▷ J = (α_ Z X J).hom ≫ ru g := E.functor.map_preimage _
      refine ⟨curry ((β_ X Z).hom ≫ q), ru_inj ?_⟩
      change ru (curry ((β_ X Z).hom ≫ q) ≫ ihomTensorBoth X Y J) = ru g
      rw [ru_s]
      simp only [ru, uncurry_curry, SymmetricCategory.symmetry_assoc]
      rw [hq, Iso.inv_hom_id_assoc]
  let (X Y : C) : IsIso (ihomTensorToIhom X Y J) :=
    isIso_ihomTensorToIhom X Y ⟨I, ⟨a⟩, ⟨b⟩⟩
  let (X Y : C) : IsIso (ihomTensorBoth X Y J) := s_iso X Y
  let t (X Y : C) := asIso (ihomTensorToIhom X Y J)
  let s (X Y : C) := asIso (ihomTensorBoth X Y J)
  have tn (X X' Y Y' : C) (f : X' ⟶ X) (g : Y ⟶ Y') :
      ((pre f).app Y ≫ (ihom X').map g) ▷ J ≫ (t X' Y').hom =
        (t X Y).hom ≫ (pre f).app (Y ⊗ J) ≫ (ihom X').map (g ▷ J) := by
    dsimp only [t, asIso_hom]
    rw [comp_whiskerRight, Category.assoc]
    have hy : (ihom X').map g ▷ J ≫ ihomTensorToIhom X' Y' J =
        ihomTensorToIhom X' Y J ≫ (ihom X').map (g ▷ J) := by
      apply uncurry_injective
      rw [uncurry_whiskerRight_comp_ihomTensorToIhom, uncurry_natural_right,
        uncurry_ihom_map, ihomTensorToIhom, uncurry_curry,
        comp_whiskerRight, Category.assoc]
    rw [hy, ← Category.assoc, pre_app_whiskerRight_comp_ihomTensorToIhom,
      Category.assoc]
  have sn (X X' Y Y' : C) (f : X' ⟶ X) (g : Y ⟶ Y') :
      ((pre f).app Y ≫ (ihom X').map g) ≫ (s X' Y').hom =
        (s X Y).hom ≫ (pre (f ▷ J)).app (Y ⊗ J) ≫
          (ihom (X' ⊗ J)).map (g ▷ J) := by
    apply ru_inj
    change ru (((pre f).app Y ≫ (ihom X').map g) ≫ ihomTensorBoth X' Y' J) =
      ru (ihomTensorBoth X Y J ≫ (pre (f ▷ J)).app (Y ⊗ J) ≫
        (ihom (X' ⊗ J)).map (g ▷ J))
    rw [ru_s, ru_pair, ru_right, ru_pre0]
    have hs := ru_s J (𝟙 ((ihom X).obj Y))
    simp only [Category.id_comp] at hs
    rw [hs]
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_inv_naturality_middle_assoc]
  refine ⟨t, s, ⟨fun X Y ↦ ⟨rfl, rfl⟩, ?_, ?_, ?_⟩⟩
  · intro X Y
    have ht := ru_t X Y J
    have hs := ru_s J (𝟙 ((ihom X).obj Y))
    simp only [Category.id_comp] at hs
    have hr {A B D : C} (f : A ⟶ (ihom B).obj D) :
        ru f = f ▷ B ≫ (β_ ((ihom B).obj D) B).hom ≫ (ihom.ev B).app D := by
      rw [← ru_id, ← ru_left, Category.comp_id]
    rw [hr] at ht hs
    rw [ru_id] at ht hs
    refine ⟨ht, hs, ?_, ?_⟩
    · rw [← ht]
      simp only [t, asIso_inv, ← Category.assoc,
        ← comp_whiskerRight, IsIso.inv_hom_id, id_whiskerRight, Category.id_comp]
    · rw [← hs]
      simp only [s, asIso_inv, ← Category.assoc,
        ← comp_whiskerRight, IsIso.inv_hom_id, id_whiskerRight, Category.id_comp]
  · intro X X' Y Y' f g
    refine ⟨tn X X' Y Y' f g, sn X X' Y Y' f g, ?_, ?_⟩
    · apply (cancel_mono (t X' Y').hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [tn, Iso.inv_hom_id_assoc]
    · apply (cancel_mono (s X' Y').hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← Category.assoc ((pre f).app Y) ((ihom X').map g) (s X' Y').hom,
        sn, Iso.inv_hom_id_assoc]
  · intro X Y J' z
    constructor
    · apply uncurry_injective
      rw [uncurry_natural_left, uncurry_natural_right]
      simp only [t, asIso_hom, ihomTensorToIhom, uncurry_curry]
      rw [associator_inv_naturality_right_assoc, whisker_exchange, Category.assoc]
      rfl
    · apply ru_inj
      dsimp only [s, asIso_hom]
      rw [ru_pair]
      have hs := ru_s J (𝟙 ((ihom X).obj Y))
      have hs' := ru_s J' (𝟙 ((ihom X).obj Y))
      simp only [Category.id_comp] at hs hs'
      change ru (ihomTensorBoth X Y J') =
        (ihom X).obj Y ◁ (X ◁ z.inv) ≫ ru (ihomTensorBoth X Y J) ≫ Y ◁ z.hom
      rw [hs, hs']
      simp only [Category.assoc]
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
      simp only [← MonoidalCategory.whiskerLeft_comp,
        Iso.inv_hom_id, whiskerLeft_id, Category.comp_id]

end CategoryTheory.MonoidalClosed
