/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.IntegrallyClosed.DepthTwo

/-!
# Regular pairs avoiding a prime in normal local rings of dimension at least two

Let `A` be a Noetherian integrally closed local domain of Krull dimension at least two, `a ≠ 0` in
the maximal ideal and `𝔭` a prime not containing the maximal ideal. Then there is `b` in the
maximal ideal, outside `𝔭`, such that `[a, b]` is a regular sequence
(`IsIntegrallyClosed.exists_isWeaklyRegular_pair_of_not_le`). This refines
`IsIntegrallyClosed.exists_isWeaklyRegular_pair` (Serre's criterion, [Stacks 031S]); the extra
prime is added to the prime avoidance.

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace IsIntegrallyClosed

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  [IsIntegrallyClosed A]

/-- **Regular pairs avoiding a prime.** In a Noetherian integrally closed local domain of dimension
at least two, every nonzero `a` in the maximal ideal is the first term of a regular sequence
`[a, b]` with `b` in the maximal ideal but outside a given prime `𝔭 ⊉ 𝔪`. -/
theorem exists_isWeaklyRegular_pair_of_not_le (h : 2 ≤ ringKrullDim A) {a : A}
    (ha : a ∈ maximalIdeal A) (ha0 : a ≠ 0) (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭 : ¬ maximalIdeal A ≤ 𝔭) :
    ∃ b ∈ maximalIdeal A, b ∉ 𝔭 ∧ b ≠ 0 ∧ RingTheory.Sequence.IsWeaklyRegular A [a, b] := by
  classical
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
  -- prime avoidance, with the extra prime `𝔭`
  let s : Finset (Ideal A) := insert 𝔭 hfin.toFinset
  have hprime : ∀ p ∈ s, p.IsPrime := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · infer_instance
    · exact (AssociatedPrimes.mem_iff.1 ((Set.Finite.mem_toFinset _).1 hp)).isPrime
  have havoid : ¬ ((maximalIdeal A : Set A) ⊆
      ⋃ p ∈ (↑s : Set (Ideal A)), ((fun p : Ideal A ↦ p) p : Set A)) := by
    intro hsub
    obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime (s := s) (f := fun p : Ideal A ↦ p) ⊥ ⊥
      (fun p hp _ _ ↦ hprime p hp)).1 hsub
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact h𝔭 hle
    · exact hnot p ((Set.Finite.mem_toFinset _).1 hp) hle
  rw [Set.not_subset] at havoid
  obtain ⟨b, hb, hbnot⟩ := havoid
  have hb𝔭 : b ∉ 𝔭 := fun h ↦ hbnot (Set.mem_biUnion (Finset.mem_insert_self _ _) h)
  have hQ : Nontrivial Q := by
    refine Submodule.Quotient.nontrivial_iff.2 fun htop ↦ ?_
    have h1 : (1 : A) ∈ a • (⊤ : Submodule A A) := htop ▸ Submodule.mem_top
    obtain ⟨z, -, hz⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 h1
    exact (IsLocalRing.mem_maximalIdeal _).1 ha (IsUnit.of_mul_eq_one (b := z) (by
      rw [← hz, smul_eq_mul]))
  have hbreg : IsSMulRegular Q b := by
    intro q₁ q₂ hq
    by_contra hne
    have hz : b ∈ ⋃ p ∈ associatedPrimes A Q, p := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨q₁ - q₂, sub_ne_zero.2 hne, by rw [smul_sub, sub_eq_zero, hq]⟩
    obtain ⟨p, hp, hbp⟩ := Set.mem_iUnion₂.1 hz
    exact hbnot (Set.mem_biUnion (Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hp))
      hbp)
  have hb0 : b ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := exists_ne (0 : Q)
    exact hq (hbreg (by simp))
  refine ⟨b, hb, hb𝔭, hb0, ?_⟩
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact ⟨fun x y hxy ↦ mul_left_cancel₀ ha0 hxy, hbreg⟩

end IsIntegrallyClosed
