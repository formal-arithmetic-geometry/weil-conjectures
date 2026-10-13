/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Normal local rings of dimension at least two have depth at least two

Let `A` be a Noetherian integrally closed local domain of Krull dimension at least two. Then the
maximal ideal of `A` contains a regular sequence of length two
(`IsIntegrallyClosed.exists_isWeaklyRegular_pair`): this is the direction of Serre's criterion
needed in [Stacks 031S].

The key point (`IsIntegrallyClosed.dvd_of_forall_dvd_mul`) is that the maximal ideal is not an
associated prime of `A / aA` for `a ≠ 0`: if `𝔪 x ⊆ aA`, then `f = x / a` satisfies `f 𝔪 ⊆ A`;
either `f 𝔪 ⊆ 𝔪`, and then `f` is integral, hence in `A`; or `f 𝔪 = A`, and then `𝔪` is
principal, which contradicts `dim A ≥ 2` by Krull's principal ideal theorem.
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace IsIntegrallyClosed

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

/-- In a Noetherian local ring of dimension at least two the maximal ideal is not principal. -/
lemma not_isPrincipal_maximalIdeal (h : 2 ≤ ringKrullDim A) :
    ¬ (maximalIdeal A).IsPrincipal := by
  intro hp
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (maximalIdeal A)
    (maximalIdeal A) (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [← h2] at h
  have h3 : ((maximalIdeal A).height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast h1
  have := h.trans h3
  norm_num at this

variable [IsIntegrallyClosed A]

/-- In a Noetherian integrally closed local domain of dimension at least two, if `a ≠ 0` divides
`y x` for every `y` in the maximal ideal, then `a` divides `x`. -/
lemma dvd_of_forall_dvd_mul (h : 2 ≤ ringKrullDim A) {a x : A} (ha : a ≠ 0)
    (hx : ∀ y ∈ maximalIdeal A, a ∣ y * x) : a ∣ x := by
  choose w hw using hx
  by_cases hint : ∀ y (hy : y ∈ maximalIdeal A), w y hy ∈ maximalIdeal A
  · let K := FractionRing A
    let f : K := algebraMap A K x / algebraMap A K a
    have ha' : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) (maximalIdeal A)
    have hN : N ≠ ⊥ := by
      intro hN
      have hm : maximalIdeal A ≠ ⊥ := fun hm ↦ not_isPrincipal_maximalIdeal h
        ⟨⟨0, by simp [hm]⟩⟩
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      have : algebraMap A K y ∈ N := Submodule.mem_map_of_mem hy
      rw [hN, Submodule.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective A K)] at this
      exact hy0 this
    have hfy (y : A) (hy : y ∈ maximalIdeal A) : f * algebraMap A K y = algebraMap A K (w y hy) := by
      rw [div_mul_eq_mul_div, div_eq_iff ha', ← map_mul, ← map_mul, mul_comm x, hw y hy,
        mul_comm]
    have hint' : IsIntegral A f := by
      refine isIntegral_of_smul_mem_submodule N hN ((maximalIdeal A).fg_of_isNoetherianRing.map _)
        f fun n hn ↦ ?_
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
      rw [smul_eq_mul, Algebra.linearMap_apply, hfy y hy]
      exact Submodule.mem_map_of_mem (hint y hy)
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
    refine ⟨z, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hz, mul_div_cancel₀ _ ha']
  · push_neg at hint
    obtain ⟨y, hy, hwy⟩ := hint
    have hu : IsUnit (w y hy) := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hwy
    exfalso
    refine not_isPrincipal_maximalIdeal h ⟨⟨y, le_antisymm (fun z hz ↦ ?_) ?_⟩⟩
    · rw [Submodule.mem_span_singleton]
      refine ⟨w z hz * ↑hu.unit⁻¹, ?_⟩
      have : y * w z hz = z * w y hy := by
        apply mul_left_cancel₀ ha
        calc a * (y * w z hz) = y * (a * w z hz) := by ring
          _ = y * (z * x) := by rw [← hw z hz]
          _ = z * (y * x) := by ring
          _ = a * (z * w y hy) := by rw [hw y hy]; ring
      rw [smul_eq_mul, mul_comm, ← mul_assoc, this, mul_assoc, IsUnit.mul_val_inv, mul_one]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hy

/-- **Serre's criterion, depth part** ([Stacks 031S] for `S₂`): a Noetherian integrally closed
local domain of dimension at least two contains a regular sequence `a, b` of length two in its
maximal ideal. -/
theorem exists_isWeaklyRegular_pair (h : 2 ≤ ringKrullDim A) :
    ∃ a ∈ maximalIdeal A, ∃ b ∈ maximalIdeal A, a ≠ 0 ∧ b ≠ 0 ∧
      RingTheory.Sequence.IsWeaklyRegular A [a, b] := by
  classical
  have hm : maximalIdeal A ≠ ⊥ := fun hm ↦ not_isPrincipal_maximalIdeal h
    ⟨⟨0, by simp [hm]⟩⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  let Q := QuotSMulTop a A
  have hfin := associatedPrimes.finite A Q
  -- the maximal ideal is not contained in an associated prime of `A / aA`
  have hnot : ∀ p ∈ associatedPrimes A Q, ¬ maximalIdeal A ≤ p := by
    intro p hp hle
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
    obtain ⟨hpp, q, hq⟩ := hp
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hdvd : a ∣ x := dvd_of_forall_dvd_mul h ha0 fun y hy ↦ by
      have : y ∈ Submodule.colon (⊥ : Submodule A Q) {Submodule.Quotient.mk x} := hq ▸ hle hy
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at this
      obtain ⟨z, -, hz⟩ := this
      exact ⟨z, by rw [← smul_eq_mul, ← hz, smul_eq_mul]⟩
    have hx0 : (Submodule.Quotient.mk x : Q) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      obtain ⟨z, rfl⟩ := hdvd
      exact ⟨z, Submodule.mem_top, rfl⟩
    rw [hx0] at hq
    refine hpp.ne_top (eq_top_iff.2 fun r _ ↦ ?_)
    rw [hq, Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  -- prime avoidance
  have havoid : ¬ ((maximalIdeal A : Set A) ⊆
      ⋃ p ∈ (↑hfin.toFinset : Set (Ideal A)), ((fun p : Ideal A ↦ p) p : Set A)) := by
    intro hsub
    obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime (s := hfin.toFinset)
      (f := fun p : Ideal A ↦ p) ⊥ ⊥ (fun p hp _ _ ↦
        (AssociatedPrimes.mem_iff.1 ((Set.Finite.mem_toFinset _).1 hp)).isPrime)).1 hsub
    exact hnot p ((Set.Finite.mem_toFinset _).1 hp) hle
  rw [Set.not_subset] at havoid
  obtain ⟨b, hb, hbnot⟩ := havoid
  have hQ : Nontrivial Q := by
    refine Submodule.Quotient.nontrivial_iff.2 fun htop ↦ ?_
    have h1 : (1 : A) ∈ a • (⊤ : Submodule A A) := htop ▸ Submodule.mem_top
    obtain ⟨z, -, hz⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 h1
    exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_mul_eq_one a z (by
      rw [← hz, smul_eq_mul]))
  have hbreg : IsSMulRegular Q b := by
    intro q₁ q₂ hq
    by_contra hne
    have hz : b ∈ ⋃ p ∈ associatedPrimes A Q, p := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨q₁ - q₂, sub_ne_zero.2 hne, by rw [smul_sub]; exact sub_eq_zero.2 hq⟩
    apply hbnot
    simpa using hz
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := exists_ne (0 : Q)
    exact hq (hbreg (by simp))
  refine ⟨a, ha, b, hb, ha0, hb0, ?_⟩
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact ⟨fun x y hxy ↦ mul_left_cancel₀ ha0 hxy, hbreg⟩

end IsIntegrallyClosed
