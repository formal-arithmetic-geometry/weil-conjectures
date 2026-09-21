/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.Mathlib.Algebra.Algebra.Tower
public import WeilConjectures.Mathlib.Algebra.Module.Torsion.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Finite families in the cotangent space of a local ring

Let `A` be a local ring with maximal ideal `𝔪` and residue field `κ`.  A finite family
`f : σ → 𝔪` has linearly independent classes in the cotangent space `𝔪 ⧸ 𝔪 ^ 2` exactly when
every relation `∑ aᵢ fᵢ ∈ 𝔪 ^ 2` has all its coefficients in `𝔪`; and such a family can be
completed to a generating family of `𝔪` by `dim_κ (𝔪 ⧸ 𝔪 ^ 2) - #σ` further elements.

An ideal `I` of `A` with `𝔪 * I = ⊥` is likewise a `κ`-vector space, and a `κ`-basis of it lifts
to a family of elements of `A` which spans `I` and whose only relations have all their
coefficients in `𝔪`.

## Main results

* `IsLocalRing.linearIndependent_toCotangent_iff`: the criterion for linear independence in the
  cotangent space.
* `IsLocalRing.exists_span_union_range_eq_maximalIdeal`: the completion to a generating family
  of the maximal ideal.
* `IsLocalRing.exists_span_eq_of_maximalIdeal_mul_eq_bot`: a `κ`-basis of an ideal annihilated
  by `𝔪`, read as a spanning family with coefficients of every relation in `𝔪`.
-/

@[expose] public section

universe u

namespace IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] {σ : Type*}

/-- The class in the cotangent space of a linear combination `∑ aᵢ fᵢ` of elements of the maximal
ideal is the corresponding combination of the classes of the `fᵢ`. -/
theorem toCotangent_sum_mul [Fintype σ] (f : σ → A) (hmem : ∀ i, f i ∈ maximalIdeal A) (a : σ → A)
    (hsum : ∑ i, a i * f i ∈ maximalIdeal A) :
    (maximalIdeal A).toCotangent ⟨∑ i, a i * f i, hsum⟩
      = ∑ i, a i • (maximalIdeal A).toCotangent ⟨f i, hmem i⟩ := by
  have hsmul : (⟨∑ i, a i * f i, hsum⟩ : maximalIdeal A)
      = ∑ i, a i • (⟨f i, hmem i⟩ : maximalIdeal A) := by
    ext
    simp
  rw [hsmul, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ map_smul _ _ _

/-- A finite family of elements of the maximal ideal of a local ring is linearly independent
in the cotangent space if and only if every relation `∑ aᵢ fᵢ ∈ 𝔪 ^ 2` has all `aᵢ ∈ 𝔪`. -/
theorem linearIndependent_toCotangent_iff [Fintype σ] (f : σ → A)
    (hmem : ∀ i, f i ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
        (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩) ↔
      ∀ a : σ → A, (∑ i, a i * f i) ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A := by
  have hsum : ∀ a : σ → A, ∑ i, a i * f i ∈ maximalIdeal A := fun a ↦
    Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hmem i)
  have hsur : Function.Surjective (algebraMap A (ResidueField A)) := by
    rw [ResidueField.algebraMap_eq]
    exact residue_surjective
  -- a relation with coefficients `a` in `A` is the class of `∑ aᵢ fᵢ` in the cotangent space
  have key (a : σ → A) : ∑ i, a i • (maximalIdeal A).toCotangent ⟨f i, hmem i⟩ =
      (maximalIdeal A).toCotangent ⟨∑ i, a i * f i, hsum a⟩ :=
    (toCotangent_sum_mul f hmem a (hsum a)).symm
  simp only [Fintype.linearIndependent_iff_forall_mem_ker_algebraMap hsur, key,
    Ideal.toCotangent_eq_zero, ResidueField.algebraMap_eq, ker_residue]

/-- A finite family in the maximal ideal of a Noetherian local ring whose classes in the
cotangent space are linearly independent extends to a generating family of the maximal ideal
by adjoining `dim_κ (𝔪 ⧸ 𝔪 ^ 2) - #σ` further elements. -/
theorem exists_span_union_range_eq_maximalIdeal [IsNoetherianRing A] [Finite σ] (f : σ → A)
    (hmem : ∀ i, f i ∈ maximalIdeal A)
    (hli : LinearIndependent (ResidueField A)
      (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩)) :
    ∃ T : Set A, T.Finite ∧
      T.ncard + Nat.card σ ≤ Module.finrank (ResidueField A) (CotangentSpace A) ∧
      Ideal.span (T ∪ Set.range f) = maximalIdeal A := by
  set K := ResidueField A
  set V := CotangentSpace A
  set v : σ → V := fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩
  have hinj : Function.Injective v := hli.injective
  have hli' : LinearIndepOn K id (Set.range v) := (linearIndepOn_range_iff hinj id).mpr hli
  set b := hli'.extend (Set.subset_univ _)
  have hsub : Set.range v ⊆ b := hli'.subset_extend _
  have hspan : Submodule.span K b = ⊤ := by
    simpa using hli'.span_extend_eq_span (Set.subset_univ _)
  have hbas : Module.Basis b K V := Module.Basis.extend hli'
  have hcard : b.ncard = Module.finrank K V := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    exact (Module.finrank_eq_card_basis hbas).symm
  choose g hg using Ideal.toCotangent_surjective (maximalIdeal A)
  set s : Set (maximalIdeal A) :=
    Set.range (fun i ↦ (⟨f i, hmem i⟩ : maximalIdeal A)) ∪ g '' (b \ Set.range v) with hs
  have himg : (maximalIdeal A).toCotangent '' s = b := by
    rw [hs, Set.image_union, ← Set.range_comp, ← Set.image_comp]
    have h1 : (maximalIdeal A).toCotangent ∘ (fun i ↦ (⟨f i, hmem i⟩ : maximalIdeal A)) = v := rfl
    have h2 : ∀ x ∈ b \ Set.range v, ((maximalIdeal A).toCotangent ∘ g) x = x := fun x _ ↦ hg x
    rw [h1, Set.image_congr h2]
    simpa using Set.union_sdiff_cancel hsub
  have hspans : Submodule.span A s = ⊤ := by
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff, himg, hspan]
  have key : Ideal.span ((↑) '' s) = maximalIdeal A :=
    Submodule.span_image_coe_eq_self_of_span_eq_top (κ := A) (fun x ↦ ⟨x, rfl⟩) hspans
  have himg2 : ((↑) : maximalIdeal A → A) '' s
      = (fun x ↦ ((g x : maximalIdeal A) : A)) '' (b \ Set.range v) ∪ Set.range f := by
    rw [hs, Set.image_union, ← Set.range_comp, ← Set.image_comp, Set.union_comm]
    rfl
  have hbfin : b.Finite := Set.toFinite b
  refine ⟨_, hbfin.sdiff.image _, ?_, himg2 ▸ key⟩
  have hrv : (Set.range v).ncard = Nat.card σ := Set.ncard_range_of_injective (f := v) hinj
  have h3 : (b \ Set.range v).ncard = b.ncard - Nat.card σ := by
    rw [Set.ncard_sdiff hsub, hrv]
  have h4 : Nat.card σ ≤ b.ncard := by
    rw [← hrv]
    exact Set.ncard_le_ncard hsub hbfin
  calc ((fun x ↦ ((g x : maximalIdeal A) : A)) '' (b \ Set.range v)).ncard + Nat.card σ
      ≤ (b \ Set.range v).ncard + Nat.card σ := by
        gcongr
        exact Set.ncard_image_le hbfin.sdiff
    _ = Module.finrank K V := by
        rw [h3, ← hcard]
        omega

section MulEqBot

variable {B : Type u} [CommRing B] [IsLocalRing B] {I : Ideal B}

/-- **A residue-field basis of an ideal annihilated by the maximal ideal, read in `B`.** If
`𝔪 * I = ⊥` and `I` is finitely generated, a `κ`-basis of `I` lifts to a finite family `e` of
elements of `B` which spans `I` on the nose and whose relations all have their coefficients
in `𝔪`.

The two conclusions are exactly the hypotheses of
`Ideal.range_linearCombination_algebraMap` and `Ideal.ker_linearCombination_eq_pi`. -/
theorem exists_span_eq_of_maximalIdeal_mul_eq_bot (h : maximalIdeal B * I = ⊥) (hI : I.FG) :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → B),
      Ideal.span (Set.range e) = I ∧
      ∀ c : ι → B, ∑ i, c i * e i = 0 → ∀ i, c i ∈ maximalIdeal B := by
  classical
  have htors : Module.IsTorsionBySet B I (maximalIdeal B : Set B) :=
    Module.isTorsionBySet_iff_smul_eq_bot.mpr h
  let _ := Ideal.Quotient.field (maximalIdeal B)
  let _ := htors.module
  have : IsScalarTower B (B ⧸ maximalIdeal B) I := htors.isScalarTower
  have : Module.Finite B I := Module.Finite.iff_fg.mpr hI
  have : Module.Finite (B ⧸ maximalIdeal B) I :=
    Module.Finite.of_restrictScalars_finite B _ _
  -- `𝔪 * I = ⊥` makes `I` a `κ`-vector space, and it is finite dimensional since `I` is `FG`
  let b := Module.Free.chooseBasis (B ⧸ maximalIdeal B) I
  have hsur : Function.Surjective (algebraMap B (B ⧸ maximalIdeal B)) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap B (B ⧸ maximalIdeal B)) = maximalIdeal B := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  refine ⟨Module.Free.ChooseBasisIndex (B ⧸ maximalIdeal B) I, inferInstance, fun i ↦ (b i : B),
    ?_, fun c hc i ↦ hker ▸
      LinearIndependent.mem_ker_algebraMap_of_sum_mul_eq_zero b.linearIndependent hsur hc i⟩
  -- no Nakayama is needed: the scalars `B → κ` being surjective, a `κ`-spanning set of `I` is
  -- already a `B`-spanning set
  have hrange : (Set.range fun i ↦ ((b i : I) : B)) = ((↑) : I → B) '' Set.range b :=
    Set.range_comp _ _
  rw [hrange]
  exact Submodule.span_image_coe_eq_self_of_span_eq_top hsur b.span_eq

end MulEqBot

end IsLocalRing
