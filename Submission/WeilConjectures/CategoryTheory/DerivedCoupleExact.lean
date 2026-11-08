/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.CategoryTheory.ExactCouple
import Submission.WeilConjectures.CategoryTheory.DerivedCoupleKernelIdentities
import Submission.WeilConjectures.CategoryTheory.DerivedCoupleMapConstruction
import Submission.WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Exactness of derived bigraded couples

Source: Stacks Project, Homological Algebra, Lemma 12.21.2 (Tag 011R),
Definition 12.21.3 (Tag 011S), and Remark 12.21.5 (Tag 0AMJ)
(blueprint: lem-sp-derived-couple-exact).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple


private noncomputable def iterInclusion {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) :
    ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q
  | 0, p, q => 𝟙 (X.D p q)
  | n + 1, p, q => (X.pageCouple n).derivedDInclusion p q ≫ iterInclusion X n p q

private def iterAlpha {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) :
    ∀ (n : ℕ) (p q : ℤ), X.D (p + n) (q - n) ⟶ X.D p q
  | 0, p, q => eqToHom (by congr 1 <;> omega)
  | n + 1, p, q => eqToHom (by congr 1 <;> omega) ≫
      iterAlpha X n (p + 1) (q - 1) ≫ X.alpha (p + 1) (q - 1) ≫
        eqToHom (by congr 1 <;> omega)

private theorem iterAlpha_succ {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (n : ℕ) (p q : ℤ) :
    iterAlpha X (n + 1) p q =
      X.alpha (p + (n + 1 : ℕ)) (q - (n + 1 : ℕ)) ≫
        eqToHom (by congr 1 <;> omega) ≫ iterAlpha X n p q := by
  induction n generalizing p q with
  | zero =>
    simp [iterAlpha]
  | succ n ih =>
    rw [iterAlpha, ih]
    apply eq_of_heq
    simp only [Category.assoc, eqToHom_comp_heq_iff]
    apply heq_comp (by congr 1 <;> omega) (by congr 1 <;> omega) rfl
    · congr! 1 <;> omega
    · rw [iterAlpha]
      simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
      rfl

private theorem image_comp_congr {C : Type u} [Category.{v} C] [Abelian C]
    {U V W Z : C} (f : U ⟶ W) (g : V ⟶ W) (k : W ⟶ Z)
    (h : imageSubobject f = imageSubobject g) :
    imageSubobject (f ≫ k) = imageSubobject (g ≫ k) := by
  have hf : imageSubobject (f ≫ k) =
      imageSubobject ((imageSubobject f).arrow ≫ k) := by
    calc
      _ = imageSubobject (factorThruImageSubobject f ≫
          ((imageSubobject f).arrow ≫ k)) := by
        rw [← Category.assoc, imageSubobject_arrow_comp]
      _ = _ := imageSubobject_comp_of_epi _ _
  have hg : imageSubobject (g ≫ k) =
      imageSubobject ((imageSubobject g).arrow ≫ k) := by
    calc
      _ = imageSubobject (factorThruImageSubobject g ≫
          ((imageSubobject g).arrow ≫ k)) := by
        rw [← Category.assoc, imageSubobject_arrow_comp]
      _ = _ := imageSubobject_comp_of_epi _ _
  rw [hf, hg, h]

private theorem iterInclusion_mono {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (n : ℕ) (p q : ℤ) :
    Mono (iterInclusion X n p q) := by
  induction n with
  | zero => change Mono (𝟙 (X.D p q)); infer_instance
  | succ n ih =>
    have := ih
    dsimp only [iterInclusion]
    have : Mono ((X.pageCouple n).derivedDInclusion p q) := by
      unfold derivedDInclusion
      infer_instance
    infer_instance

private theorem iterInclusion_alpha {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (n : ℕ) (p q : ℤ) :
    (X.pageCouple n).alpha p q ≫ iterInclusion X n (p - 1) (q + 1) =
      iterInclusion X n p q ≫ X.alpha p q := by
  induction n with
  | zero => simp [iterInclusion, pageCouple]
  | succ n ih =>
    change ((Classical.choice (X.pageCouple n).derivedMaps_exists).alpha p q) ≫
        ((X.pageCouple n).derivedDInclusion (p - 1) (q + 1) ≫
          iterInclusion X n (p - 1) (q + 1)) = _
    rw [← Category.assoc, (Classical.choice (X.pageCouple n).derivedMaps_exists).alpha_comm,
      Category.assoc, ih]
    simp only [iterInclusion, Category.assoc]

private theorem iterInclusion_alpha_incoming
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (n : ℕ) (p q : ℤ) :
    (X.pageCouple n).alpha (p + 1) (q - 1) ≫
        eqToHom (by congr 1 <;> omega) ≫ iterInclusion X n p q =
      iterInclusion X n (p + 1) (q - 1) ≫ X.alpha (p + 1) (q - 1) ≫
        eqToHom (by congr 1 <;> omega) := by
  apply eq_of_heq
  have h := iterInclusion_alpha X n (p + 1) (q - 1)
  apply HEq.trans _ (HEq.trans (heq_of_eq h) _)
  · apply heq_comp rfl rfl (by congr 1 <;> omega) HEq.rfl
    rw [eqToHom_comp_heq_iff]
    congr! 1 <;> omega
  · simp only [← Category.assoc, heq_comp_eqToHom_iff]
    rfl

private theorem iterInclusion_image {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (n : ℕ) (p q : ℤ) :
    imageSubobject (iterInclusion X n p q) = imageSubobject (iterAlpha X n p q) := by
  induction n generalizing p q with
  | zero =>
    change imageSubobject (𝟙 (X.D p q)) = imageSubobject (eqToHom _)
    rw [imageSubobject_mono (𝟙 (X.D p q)), Subobject.mk_eq_top_of_isIso,
      imageSubobject_mono (eqToHom _), Subobject.mk_eq_top_of_isIso]
  | succ n ih =>
    let a := (X.pageCouple n).alpha (p + 1) (q - 1)
    have hfac : factorThruImage a ≫ iterInclusion X (n + 1) p q =
        a ≫ eqToHom (by congr 1 <;> omega) ≫ iterInclusion X n p q := by
      simp only [iterInclusion, derivedDInclusion, ← Category.assoc, image.fac, a]
    calc
      imageSubobject (iterInclusion X (n + 1) p q) =
          imageSubobject (factorThruImage a ≫ iterInclusion X (n + 1) p q) :=
        (imageSubobject_comp_of_epi _ _).symm
      _ = imageSubobject (iterInclusion X n (p + 1) (q - 1) ≫
          X.alpha (p + 1) (q - 1) ≫ eqToHom (by congr 1 <;> omega)) := by
        rw [hfac, iterInclusion_alpha_incoming]
      _ = imageSubobject (iterAlpha X n (p + 1) (q - 1) ≫
          X.alpha (p + 1) (q - 1) ≫ eqToHom (by congr 1 <;> omega)) :=
        image_comp_congr _ _ _ (ih (p + 1) (q - 1))
      _ = imageSubobject (iterAlpha X (n + 1) p q) := by
        symm
        exact imageSubobject_iso_comp (eqToHom _) _

/-- The recursive image and inclusion properties of iterated derived couples.
(blueprint: lem-sp-derived-couple-image-prefix)

Source: Stacks Project, Definition 12.21.3 (Tag 011S) and Remark 12.21.5 (Tag 0AMJ).

Construct `I` by composing image inclusions and `A` by appending incoming `alpha` maps.
Associativity and induction also give the prescribed recurrence prepending `alpha`.
The inclusions are mono by induction. The `DerivedMaps.alpha_comm` equation gives
compatibility with the original `alpha`, again by induction. For the image induction,
precompose the next inclusion with the epimorphic factorization of the incoming
page-`alpha`. Compatibility identifies this composite with the previous inclusion
followed by the original `alpha`. Factoring maps through their image subobjects shows
that equal image subobjects remain equal after postcomposition. Apply the induction
hypothesis and the appended-alpha recurrence. Index transports are isomorphisms and
do not change images. The base case consists of identity maps with image the top
subobject; it includes all integer bidegrees without a positivity assumption. -/
theorem pageCouple_image_prefix {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) :
    ∃ (A : ∀ (n : ℕ) (p q : ℤ), X.D (p + n) (q - n) ⟶ X.D p q)
      (I : ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q),
      (∀ p q : ℤ, A 0 p q = eqToHom (by congr 1 <;> omega)) ∧
      (∀ (n : ℕ) (p q : ℤ), A (n + 1) p q =
        X.alpha (p + (n + 1 : ℕ)) (q - (n + 1 : ℕ)) ≫
          eqToHom (by congr 1 <;> omega) ≫ A n p q) ∧
      (∀ p q : ℤ, I 0 p q = 𝟙 (X.D p q)) ∧
      (∀ (n : ℕ) (p q : ℤ), I (n + 1) p q =
        (X.pageCouple n).derivedDInclusion p q ≫ I n p q) ∧
      (∀ (n : ℕ) (p q : ℤ), Mono (I n p q)) ∧
      (∀ (n : ℕ) (p q : ℤ), imageSubobject (I n p q) = imageSubobject (A n p q)) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (X.pageCouple n).alpha p q ≫ I n (p - 1) (q + 1) =
          I n p q ≫ X.alpha p q) := by
  refine ⟨iterAlpha X, iterInclusion X, ?_, iterAlpha_succ X, ?_, ?_,
    iterInclusion_mono X, iterInclusion_image X, iterInclusion_alpha X⟩
  · intro p q
    rfl
  · intro p q
    rfl
  · intro n p q
    rfl


/-- Iterated derived couples are the images of the iterated `alpha` maps.
Here `n` is `r - 2`: the actual page number is `n + 2`. The quantified families
`A` and `I` are uniquely prescribed by their recurrences: `A` is the incoming
`alpha` power and `I` is the composite of all the canonical image inclusions.
Source: Stacks Project, Tags 011S and 0AMJ (blueprint: lem-sp-derived-couple-exact).

Proof (step 11 of the node). Use `pageCouple_image_prefix` for the recursive powers,
monomorphic inclusions, image formula, and compatibility with the original `alpha`.
Its proof inducts on `n` using `DerivedMaps.alpha_comm` and image factorizations.
The `E` recurrence is precisely the
cokernel of the incoming differential lifted into the outgoing kernel, hence cycles
modulo boundaries. The types of `pageCouple`, its `alpha`, `f`, `g`, and `d` give
respectively type `n = r-2` and bidegrees `(-1,1)`, `(2,-1)`, `(n,-n)` and
`(n+2,-n-1) = (r,1-r)`. This proves every asserted recurrence and image formula. -/
theorem pageCouple_image {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) :
    ∃ (A : ∀ (n : ℕ) (p q : ℤ), X.D (p + n) (q - n) ⟶ X.D p q)
      (I : ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q),
      (∀ p q : ℤ, A 0 p q = eqToHom (by congr 1 <;> omega)) ∧
      (∀ (n : ℕ) (p q : ℤ), A (n + 1) p q =
        X.alpha (p + (n + 1 : ℕ)) (q - (n + 1 : ℕ)) ≫
          eqToHom (by congr 1 <;> omega) ≫ A n p q) ∧
      (∀ p q : ℤ, I 0 p q = 𝟙 (X.D p q)) ∧
      (∀ (n : ℕ) (p q : ℤ), I (n + 1) p q =
        (X.pageCouple n).derivedDInclusion p q ≫ I n p q) ∧
      (∀ (n : ℕ) (p q : ℤ), Mono (I n p q)) ∧
      (∀ (n : ℕ) (p q : ℤ), imageSubobject (I n p q) = imageSubobject (A n p q)) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (X.pageCouple n).alpha p q ≫ I n (p - 1) (q + 1) =
          I n p q ≫ X.alpha p q) ∧
      (∀ (n : ℕ) (p q : ℤ), (X.pageCouple (n + 1)).E p q =
        cokernel (kernel.lift ((X.pageCouple n).d p q)
          ((X.pageCouple n).dInto p q) ((X.pageCouple n).dInto_comp_d p q))) := by
  obtain ⟨A, I, h⟩ := pageCouple_image_prefix X
  refine ⟨A, I, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2, ?_⟩
  intro n p q
  rfl

end CategoryTheory.BigradedExactCouple
