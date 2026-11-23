/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.DerivedCoupleKernelIdentities
import WeilConjectures.CategoryTheory.DerivedCoupleMapUniqueness
import WeilConjectures.CategoryTheory.DerivedCoupleBoundaryVanishes
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Exactness of derived bigraded couples

Source: Stacks Project, Homological Algebra, Lemma 12.21.2 (Tag 011R),
Definition 12.21.3 (Tag 011S), and Remark 12.21.5 (Tag 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

/-- Kernel and image identities, and unique induced exact maps, for a type-`s` couple.
Source: Stacks Project, Tags 011R and 0AMJ. -/
theorem derived_couple_exact {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    (∀ p q : ℤ,
      let a : X.D (p + 3) (q - 2) ⟶ X.D (p + 2) (q - 1) :=
        X.alpha (p + 3) (q - 2) ≫ eqToHom (by congr 1 <;> omega)
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (kernelSubobject (X.g (p + 2) (q - 1))) ∧
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (imageSubobject a) ∧
      kernelSubobject (X.g (p + 2) (q - 1)) = imageSubobject a ∧
      imageSubobject (X.d p q) =
          imageSubobject ((imageSubobject (X.f p q)).arrow ≫ X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.d p q) =
          imageSubobject
            ((kernelSubobject (X.alpha (p + 2) (q - 1))).arrow ≫
              X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.f p q) = kernelSubobject (X.alpha (p + 2) (q - 1)) ∧
      imageSubobject (kernel.ι (X.d p q) ≫ X.f p q) ≤ imageSubobject a) ∧
    (∀ p q : ℤ,
      X.gToCycles p q ≫ kernel.ι (X.d (p + s) (q - s)) = X.g p q) ∧
    (∀ p q : ℤ, X.d p q ≫ X.d (p + 2 + s) (q - 1 - s) = 0) ∧
    (∀ p q : ℤ,
      kernel.ι (factorThruImage (X.alpha (p + 1) (q - 1))) ≫
        X.gToCycles (p + 1) (q - 1) ≫
          X.derivedEProjection ((p + 1) + s) ((q - 1) - s) = 0) ∧
    (∃ M : DerivedMaps X,
      (∀ (p q : ℤ) (a : X.derivedD p q ⟶ X.derivedD (p - 1) (q + 1)),
        a ≫ X.derivedDInclusion (p - 1) (q + 1) = X.derivedDInclusion p q ≫ X.alpha p q →
          a = M.alpha p q) ∧
      (∀ (p q : ℤ) (b : X.derivedE p q ⟶ X.derivedD (p + 2) (q - 1)),
        X.derivedEProjection p q ≫ b ≫ X.derivedDInclusion (p + 2) (q - 1) =
            kernel.ι (X.d p q) ≫ X.f p q →
          b = M.f p q) ∧
      (∀ (p q : ℤ) (c : X.derivedD p q ⟶ X.derivedE (p + (s + 1)) (q - (s + 1))),
        factorThruImage (X.alpha (p + 1) (q - 1)) ≫ c =
            X.gToCycles (p + 1) (q - 1) ≫
              X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫
                eqToHom (by congr 1 <;> omega) →
          c = M.g p q))  := by
  have hk := derived_couple_kernel_identities X
  obtain ⟨M, hM⟩ := derived_couple_map_uniqueness X
  refine ⟨hk, ?_, ?_, ?_, ⟨M, hM.1, hM.2.1, hM.2.2⟩⟩
  · intro p q
    simp [gToCycles]
  · intro p q
    exact X.d_comp_d p q
  · exact derived_couple_boundary_vanishes X


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

Source: Stacks Project, Definition 12.21.3 (Tag 011S) and Remark 12.21.5 (Tag 0AMJ). -/
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
Source: Stacks Project, Tags 011S and 0AMJ. -/
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
