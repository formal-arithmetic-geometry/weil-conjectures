/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Internal-Hom cancellation by an invertible tensor factor

Source: Stacks Project, Categories, Tags 0FFM and 0GWJ; their evaluation-normalized
consequence (blueprint: lem-sf-invertible-factor-hom-cancellation).

## Main definitions

- `CategoryTheory.MonoidalClosed.ihomTensorBoth`: simultaneous tensoring of the two arguments.

## Main statements

- `CategoryTheory.MonoidalClosed.invertibleFactorHomCancellation`: the two canonical
  transposes are isomorphisms, with variable naturality, factor compatibility, and the
  evaluation equations for their forward and inverse maps.

Mathlib places the argument of internal Hom on the left of evaluation. The evaluation
`[X,Y] ⊗ X ⟶ Y` of Tag 0GWJ is therefore `(β_ _ X).hom ≫ (ihom.ev X).app Y`.
The same symmetry transports the chosen adjunction to tensoring on the right. No
additional choice of internal Hom or evaluation is made here.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C]

/-- Simultaneous tensoring `[X,Y] ⟶ [X ⊗ J,Y ⊗ J]`, defined by transposing evaluation
with an identity on `J`. Source: Stacks Project, Tags 0FFM and 0GWJ
(blueprint: lem-sf-invertible-factor-hom-cancellation).
This construction uses no inverse-factor data. The braiding moves `J` past `[X,Y]`,
and the associators put `X` and `[X,Y]` next to one another for evaluation. -/
noncomputable def ihomTensorBoth (X Y J : C) :
    (ihom X).obj Y ⟶ (ihom (X ⊗ J)).obj (Y ⊗ J) :=
  curry ((α_ X J ((ihom X).obj Y)).hom ≫
    X ◁ (β_ J ((ihom X).obj Y)).hom ≫
    (α_ X ((ihom X).obj Y) J).inv ≫ (ihom.ev X).app Y ▷ J)

private def rightUncurry {X Y Z : C} (f : Z ⟶ (ihom X).obj Y) : Z ⊗ X ⟶ Y :=
  (β_ Z X).hom ≫ uncurry f

private theorem rightUncurry_eq {X Y Z : C} (f : Z ⟶ (ihom X).obj Y) :
    rightUncurry f = f ▷ X ≫ (β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y := by
  simp [rightUncurry, uncurry_eq, BraidedCategory.braiding_naturality_left_assoc]

private theorem rightUncurry_injective {X Y Z : C} :
    Function.Injective (rightUncurry : (Z ⟶ (ihom X).obj Y) → (Z ⊗ X ⟶ Y)) := by
  intro f g h
  apply uncurry_injective
  exact (cancel_epi (β_ Z X).hom).1 h

private theorem rightUncurry_comp {X Y Z W : C} (f : W ⟶ Z)
    (g : Z ⟶ (ihom X).obj Y) :
    rightUncurry (f ≫ g) = f ▷ X ≫ rightUncurry g := by
  simp [rightUncurry, uncurry_natural_left, ← BraidedCategory.braiding_naturality_left_assoc]

private theorem rightUncurry_map {X Y Y' Z : C} (f : Z ⟶ (ihom X).obj Y)
    (g : Y ⟶ Y') :
    rightUncurry (f ≫ (ihom X).map g) = rightUncurry f ≫ g := by
  simp [rightUncurry, uncurry_natural_right]

private theorem rightUncurry_pre {X X' Y Z : C} (f : Z ⟶ (ihom X).obj Y)
    (g : X' ⟶ X) :
    rightUncurry (f ≫ (pre g).app Y) = Z ◁ g ≫ rightUncurry f := by
  simp [rightUncurry, uncurry_pre_app, BraidedCategory.braiding_naturality_right_assoc]

private theorem tensorTo_eval (X Y J : C) :
    rightUncurry (ihomTensorToIhom X Y J) =
      (α_ ((ihom X).obj Y) J X).hom ≫
        (ihom X).obj Y ◁ (β_ J X).hom ≫ (α_ ((ihom X).obj Y) X J).inv ≫
        ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J := by
  simp only [rightUncurry, ihomTensorToIhom, uncurry_curry,
    BraidedCategory.braiding_tensor_left_hom, Category.assoc, comp_whiskerRight]
  monoidal

private theorem tensorBoth_eval (X Y J : C) :
    rightUncurry (ihomTensorBoth X Y J) =
      (α_ ((ihom X).obj Y) X J).inv ≫
        ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J := by
  simp only [rightUncurry, ihomTensorBoth, uncurry_curry,
    BraidedCategory.braiding_tensor_right_hom, Category.assoc, comp_whiskerRight]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Iso.inv_hom_id_assoc]
  monoidal

private theorem rightUncurry_bijective (X Y Z : C) :
    Function.Bijective (rightUncurry : (Z ⟶ (ihom X).obj Y) → (Z ⊗ X ⟶ Y)) := by
  refine ⟨rightUncurry_injective, fun f ↦ ?_⟩
  refine ⟨curry ((β_ X Z).hom ≫ f), ?_⟩
  simp [rightUncurry]

private theorem tensorBoth_comp {X Y Z : C} (J : C) (f : Z ⟶ (ihom X).obj Y) :
    rightUncurry (f ≫ ihomTensorBoth X Y J) =
      (α_ Z X J).inv ≫ rightUncurry f ▷ J := by
  rw [rightUncurry_comp, tensorBoth_eval]
  simp only [rightUncurry, uncurry_eq, comp_whiskerRight]
  rw [associator_inv_naturality_left_assoc]
  simp only [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left,
    comp_whiskerRight]

private theorem tensorBoth_isIso (J I : C) (a : J ⊗ I ≅ 𝟙_ C)
    (b : I ⊗ J ≅ 𝟙_ C) (X Y : C) : IsIso (ihomTensorBoth X Y J) := by
  let E := tensorRightEquivalenceOfTensorIso a b
  refine isIso_of_yoneda_map_bijective _ (fun Z ↦ ⟨?_, ?_⟩)
  · intro f g h
    apply rightUncurry_injective
    apply E.functor.map_injective
    change rightUncurry f ▷ J = rightUncurry g ▷ J
    apply (cancel_epi (α_ Z X J).inv).1
    simpa only [← tensorBoth_comp] using congrArg rightUncurry h
  · intro g
    let d : Z ⊗ X ⟶ Y := E.functor.preimage ((α_ Z X J).hom ≫ rightUncurry g)
    obtain ⟨f, hf⟩ := (rightUncurry_bijective X Y Z).2 d
    refine ⟨f, rightUncurry_injective ?_⟩
    rw [tensorBoth_comp, hf]
    have hd : d ▷ J = (α_ Z X J).hom ≫ rightUncurry g := E.functor.map_preimage _
    rw [hd, Iso.inv_hom_id_assoc]

omit [SymmetricCategory C] in
private theorem tensorTo_natural (J : C) {X X' Y Y' : C}
    (f : X' ⟶ X) (g : Y ⟶ Y') :
    ((pre f).app Y ≫ (ihom X').map g) ▷ J ≫ ihomTensorToIhom X' Y' J =
      ihomTensorToIhom X Y J ≫ (pre f).app (Y ⊗ J) ≫ (ihom X').map (g ▷ J) := by
  have hmap : (ihom X').map g ▷ J ≫ ihomTensorToIhom X' Y' J =
      ihomTensorToIhom X' Y J ≫ (ihom X').map (g ▷ J) := by
    apply uncurry_injective
    rw [uncurry_whiskerRight_comp_ihomTensorToIhom, uncurry_natural_right,
      uncurry_ihom_map, ihomTensorToIhom, uncurry_curry, comp_whiskerRight,
      Category.assoc]
  rw [comp_whiskerRight, Category.assoc, hmap,
    pre_app_whiskerRight_comp_ihomTensorToIhom_assoc]

private theorem tensorBoth_natural (J : C) {X X' Y Y' : C}
    (f : X' ⟶ X) (g : Y ⟶ Y') :
    ((pre f).app Y ≫ (ihom X').map g) ≫ ihomTensorBoth X' Y' J =
      ihomTensorBoth X Y J ≫ (pre (f ▷ J)).app (Y ⊗ J) ≫
        (ihom (X' ⊗ J)).map (g ▷ J) := by
  apply rightUncurry_injective
  rw [tensorBoth_comp]
  simp only [← Category.assoc, rightUncurry_map, rightUncurry_pre]
  rw [tensorBoth_eval]
  simp only [rightUncurry, uncurry_pre, comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  simp only [← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right_assoc]

omit [SymmetricCategory C] in
private theorem tensorTo_factor (X Y J J' : C) (z : J ≅ J') :
    (ihom X).obj Y ◁ z.hom ≫ ihomTensorToIhom X Y J' =
      ihomTensorToIhom X Y J ≫ (ihom X).map (Y ◁ z.hom) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right]
  simp only [ihomTensorToIhom, uncurry_curry]
  rw [associator_inv_naturality_right_assoc, whisker_exchange]
  simp only [Functor.id_obj, Category.assoc]

private theorem tensorBoth_factor (X Y J J' : C) (z : J ≅ J') :
    ihomTensorBoth X Y J' =
      ihomTensorBoth X Y J ≫ (pre (X ◁ z.inv)).app (Y ⊗ J) ≫
        (ihom (X ⊗ J')).map (Y ◁ z.hom) := by
  apply rightUncurry_injective
  rw [← Category.assoc, rightUncurry_map, rightUncurry_pre,
    tensorBoth_eval, tensorBoth_eval]
  rw [associator_inv_naturality_right_assoc]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  simp only [Functor.id_obj, ← MonoidalCategory.whiskerLeft_comp,
    Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- Internal-Hom cancellation by an invertible tensor factor, with both forward and inverse
maps normalized by evaluation. Source: Stacks Project, Tags 0FFM and 0GWJ
(blueprint: lem-sf-invertible-factor-hom-cancellation).

The witnesses `t` and `s` are uniquely determined by the first conjunct, so these are
specified canonical isomorphisms, not arbitrary representing-object comparisons.
The cancellation isomorphism in the node is `(s X Y).symm`.

Proof plan:
1. Tensoring on the right with `J` and with `I` gives quasi-inverse functors. The composites
   are identified with the identity by the associator, `a` or `b`, and the right unitor.
   Naturality follows from the monoidal axioms; no triangle law on `a` and `b` is needed.
2. Apply `lem-sf-quasi-inverse-hom-bijection`, represented by `Equivalence.mk` and
   `Equivalence.fullyFaithfulFunctor.map_bijective`. Tensoring with `J` is fully faithful,
   and every object is isomorphic to `(Z ⊗ I) ⊗ J`.
3. Define the transposes using the closed adjunction. The first is the existing
   `ihomTensorToIhom`; the second is `ihomTensorBoth`. Uncurrying gives the two evaluation
   equations, with the right evaluation obtained by symmetry as above.
4. Test the first map on `W ⊗ J`. A map into `[X,Y] ⊗ J` uniquely equals `h ▷ J`.
   Transpose `h`, tensor with `J`, then interchange `J` and `X` using the braiding.
   Each operation is bijective, so postcomposition with this particular first map is
   bijective on these test objects.
5. Transport along `(Z ⊗ I) ⊗ J ≅ Z` to get bijectivity for every test object. Taking
   the test object to be the target gives a right inverse; injectivity at the source
   makes it also a left inverse. Thus the first map is an isomorphism.
6. For the second map, postcomposition is the chain of bijections given by transposition,
   tensoring both source and target with `J`, reassociation, and transposition back.
   The same isomorphism test proves it invertible.
7. Uncurry the two variable-naturality identities. Both sides agree by evaluation
   naturality, braiding naturality, and associator naturality. Transposition is injective.
8. For `z : J ≅ J'`, uncurry the factor-compatibility identities. The first follows from
   braiding naturality. The second uses `z.inv` in the contravariant argument and `z.hom`
   in the covariant argument; their composite cancels. The definitions do not use `a,b`.
9. Compose the defining evaluation equations with the inverse maps to obtain the inverse
   evaluation equations. Multiply the variable and factor naturality identities by
   inverses to obtain the corresponding compatibilities for the inverse isomorphisms.
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
            (ihom X).obj Y ◁ (β_ J X).hom ≫ (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J ∧
        (s X Y).hom ▷ (X ⊗ J) ≫
            (β_ ((ihom (X ⊗ J)).obj (Y ⊗ J)) (X ⊗ J)).hom ≫
            (ihom.ev (X ⊗ J)).app (Y ⊗ J) =
          (α_ ((ihom X).obj Y) X J).inv ≫
            ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y) ▷ J ∧
        (t X Y).inv ▷ X ≫ (α_ ((ihom X).obj Y) J X).hom ≫
            (ihom X).obj Y ◁ (β_ J X).hom ≫ (α_ ((ihom X).obj Y) X J).inv ≫
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
  let t (X Y : C) : (ihom X).obj Y ⊗ J ≅ (ihom X).obj (Y ⊗ J) := by
    have := isIso_ihomTensorToIhom X Y (⟨I, ⟨a⟩, ⟨b⟩⟩ : IsInvertible J)
    exact asIso (ihomTensorToIhom X Y J)
  let s (X Y : C) : (ihom X).obj Y ≅ (ihom (X ⊗ J)).obj (Y ⊗ J) := by
    have := tensorBoth_isIso J I a b X Y
    exact asIso (ihomTensorBoth X Y J)
  have ht (X Y : C) : (t X Y).hom = ihomTensorToIhom X Y J := rfl
  have hs (X Y : C) : (s X Y).hom = ihomTensorBoth X Y J := rfl
  refine ⟨t, s, fun X Y ↦ ⟨ht X Y, hs X Y⟩, ?_, ?_, ?_⟩
  · intro X Y
    have et := tensorTo_eval X Y J
    have es := tensorBoth_eval X Y J
    rw [rightUncurry_eq, ← ht] at et
    rw [rightUncurry_eq, ← hs] at es
    refine ⟨et, es, ?_, ?_⟩
    · rw [← et]
      simp only [← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
        id_whiskerRight, Category.id_comp]
    · rw [← es]
      simp only [← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
        id_whiskerRight, Category.id_comp]
  · intro X X' Y Y' f g
    have nt := tensorTo_natural J f g
    have ns := tensorBoth_natural J f g
    rw [← ht, ← ht] at nt
    rw [← hs, ← hs] at ns
    refine ⟨nt, ns, ?_, ?_⟩
    · simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.inv_hom_id_assoc] using
        (congrArg (fun k ↦ (t X Y).inv ≫ k ≫ (t X' Y').inv) nt).symm
    · simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.inv_hom_id_assoc] using
        (congrArg (fun k ↦ (s X Y).inv ≫ k ≫ (s X' Y').inv) ns).symm
  · intro X Y J' z
    constructor
    · simpa only [ht] using tensorTo_factor X Y J J' z
    · simpa only [hs] using tensorBoth_factor X Y J J' z

end CategoryTheory.MonoidalClosed
