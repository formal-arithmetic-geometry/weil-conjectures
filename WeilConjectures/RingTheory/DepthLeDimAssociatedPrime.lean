/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import WeilConjectures.RingTheory.AssociatedPrimePowerQuotient
import WeilConjectures.RingTheory.DepthQuotSMulTop
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Nakayama

/-!
# Depth is bounded by the dimension at an associated prime

For a finite module `M` over a Noetherian local ring `R` and an associated prime `p` of `M`,
`depth M ≤ dim (R/p)`.

## Implementation details

Since `R` is Noetherian, Mathlib's `associatedPrimes R M` are exactly the primes of the form
`Ann_R(z)` (`isAssociatedPrime_iff`, Tag 00LA). The proof is by induction on the depth: if the
maximal ideal is associated, the depth is zero. Otherwise pick a regular `x` in the maximal
ideal outside `p` and a minimal prime `q` over `p + (x)`; then `q` is associated to
`M/x^n M` for some `n > 0`, this quotient has depth one less, and `dim(R/q) + 1 ≤ dim(R/p)`.

## References

* [Stacks, Tag 0BK4]
* [Stacks, Tag 00LA]
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem depth_eq_zero_of_maximal_associated
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hm : maximalIdeal R ∈ associatedPrimes R M) : depth (R := R) M = 0 := by
  have hM : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  rw [depth, Ideal.depth, ite_eq_right hM]
  apply le_antisymm _ zero_le
  apply sSup_le
  rintro n ⟨rs, hrs, hmem, rfl⟩
  cases rs with
  | nil => simp
  | cons x xs =>
    have hxreg := ((RingTheory.Sequence.isRegular_cons_iff M x xs).mp hrs).1
    have hx : x ∈ maximalIdeal R := hmem x (by simp)
    have hunion : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
      Set.mem_iUnion.mpr ⟨maximalIdeal R, Set.mem_iUnion.mpr ⟨hm, hx⟩⟩
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hunion
    exact False.elim (hunion hxreg)

/-- For a finite module over a Noetherian local ring, the depth is at most the
Krull dimension of the quotient by every associated prime.
-/
theorem depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    (IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  have hnt : Nontrivial M := by
    by_contra h
    let : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    exact (not_isAssociatedPrime_of_subsingleton (I := p) (M := M)) hp
  let : Nontrivial M := hnt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, depth (R := R) M = (d : ℕ∞) := by
    by_cases hm : maximalIdeal R ∈ associatedPrimes R M
    · exact ⟨0, depth_eq_zero_of_maximal_associated M hm⟩
    · obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective R M hm
      obtain ⟨_, d, _, hd, _⟩ := depth_quotSMulTop_of_isSMulRegular M x hx hreg
      exact ⟨d, hd⟩
  have hind : ∀ (d : ℕ) (N : Type v) [AddCommGroup N] [Module R N]
      [Module.Finite R N] [Nontrivial N], depth (R := R) N = (d : ℕ∞) →
      ∀ (p : Ideal R), p ∈ associatedPrimes R N →
        (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
    intro d
    induction d with
    | zero =>
      intro N _ _ _ _ hdep p hp
      let : p.IsPrime := hp.isPrime
      exact ringKrullDim_nonneg_of_nontrivial
    | succ d ih =>
      intro N _ _ _ _ hdep p hp
      have hm : maximalIdeal R ∉ associatedPrimes R N := by
        intro hm
        have hz := depth_eq_zero_of_maximal_associated N hm
        rw [hdep] at hz
        simp at hz
      obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective R N hm
      have hxp : x ∉ p := by
        intro hxp
        have hunion : x ∈ ⋃ p ∈ associatedPrimes R N, (p : Set R) :=
          Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hxp⟩⟩
        rw [biUnion_associatedPrimes_eq_compl_regular R N] at hunion
        exact hunion hreg
      have hpm : p ≤ maximalIdeal R := le_maximalIdeal hp.isPrime.ne_top
      obtain ⟨q, hq, _⟩ := Ideal.exists_minimalPrimes_le
        (J := maximalIdeal R) (sup_le hpm ((Ideal.span_singleton_le_iff_mem _).mpr hx))
      obtain ⟨n, hn, hqa⟩ := Module.exists_mem_associatedPrimes_quotient_pow x hx p q hp hq
      have hxpow : x ^ n ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ hx n (by omega)
      obtain ⟨hntq, e, he, hde, hqe⟩ :=
        depth_quotSMulTop_of_isSMulRegular N (x ^ n) hxpow (hreg.pow n)
      let : Nontrivial (QuotSMulTop (x ^ n) N) := hntq
      have hed : e = d + 1 := by
        rw [hdep] at hde
        exact_mod_cast hde.symm
      have hqd : depth (R := R) (QuotSMulTop (x ^ n) N) = (d : ℕ∞) := by
        simpa [hed] using hqe
      have hi := ih (QuotSMulTop (x ^ n) N) hqd q hqa
      have hpq : p ≤ q := le_sup_left.trans hq.1.2
      have hxq : x ∈ q :=
        hq.1.2 ((show Ideal.span {x} ≤ p ⊔ Ideal.span {x} from le_sup_right)
          (Ideal.subset_span (by simp)))
      let : p.IsPrime := hp.isPrime
      have hdimpq : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
        apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq)
          (Ideal.Quotient.factor_surjective hpq)
          (r := Ideal.Quotient.mk p x)
        · exact mem_nonZeroDivisors_iff_ne_zero.mpr
            (fun heq ↦ hxp (Ideal.Quotient.eq_zero_iff_mem.mp heq))
        · simpa only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxq
      calc
        ((d + 1 : ℕ) : WithBot ℕ∞) = (d : WithBot ℕ∞) + 1 := by simp
        _ ≤ ringKrullDim (R ⧸ q) + 1 := by simpa only [add_comm] using add_le_add_right hi 1
        _ ≤ ringKrullDim (R ⧸ p) := hdimpq
  rw [hd]
  exact hind d M hd p hp

end IsLocalRing
