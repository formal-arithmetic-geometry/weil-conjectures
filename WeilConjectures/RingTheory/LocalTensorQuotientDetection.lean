/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.LocalTensorQuotientPowerBound
import WeilConjectures.RingTheory.LocalTensorQuotientBaseIdealDetection
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Finite quotient detection by prime localizations

For `S` finite over a Noetherian ring `R`, an element of `(R_p/m^n) ⊗_R S` vanishes if its images
in `S_q/N_q^k` vanish for all primes `q` over `p`, for some sufficiently large `k`.

## Implementation details

`B/m^n B`, for `B = R_p ⊗_R S`, is Artinian and hence the product of the rings `S_q/m^n S_q`.
In each `S_q` the ideal `m S_q` has radical the maximal ideal `N_q`, so `N_q^{c_q} ⊆ m S_q`; any
`k ≥ n c_q` for all `q` works.

## References

* [Stacks, Tag 07N9]
* [Stacks, Tags 00JA, 00CT, 0394]
-/

@[expose] public section

universe u v w
open scoped TensorProduct
namespace AdicCompletion

/-- Sufficiently deep local maximal-ideal reductions detect any fixed tensor quotient. -/
theorem local_tensor_quotient_detection
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let Q := p.primesOver S
    ∃ k : ℕ, n ≤ k ∧ ∀ (ι : Type w) (t : Finset ι) (r : ι → A) (s : ι → S),
      (∀ q : Q,
        ∑ i ∈ t, Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ k)
          (Localization.localRingHom p q.1 (algebraMap R S)
            (Ideal.LiesOver.over (P := q.1) (p := p)) (r i) *
            algebraMap S (Localization.AtPrime q.1) (s i)) = 0) →
      (∑ i ∈ t, (Ideal.Quotient.mk (m ^ n) (r i)) ⊗ₜ[R] s i) = 0 := by
  dsimp
  by_cases hn : n = 0
  · subst n
    refine ⟨0, le_rfl, ?_⟩
    intro ι t r s _h
    apply Finset.sum_eq_zero
    intro i _hi
    rw [pow_zero]
    rw [show Ideal.Quotient.mk (1 : Ideal (Localization.AtPrime p)) (r i) = 0 by
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      simp]
    exact TensorProduct.zero_tmul _ _
  · obtain ⟨c, hc, hbound⟩ := local_tensor_quotient_power_bound R S p
    refine ⟨n * c, ?_, ?_⟩
    · calc
        n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * c := Nat.mul_le_mul_left n hc
    · intro ι t r s h
      apply local_tensor_quotient_base_ideal_detection R S p n (Nat.pos_of_ne_zero hn)
        ι t r s
      intro q
      have hmem := (Ideal.Quotient.eq_zero_iff_mem).mp
        (show Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ (n * c))
          (∑ i ∈ t, Localization.localRingHom p q.1 (algebraMap R S)
            (Ideal.LiesOver.over (P := q.1) (p := p)) (r i) *
            algebraMap S (Localization.AtPrime q.1) (s i)) = 0 by
          simpa only [map_sum] using h q)
      have hpow : (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ (n * c) ≤
          (IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ n).map
            (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p))) := by
        rw [Nat.mul_comm n c, pow_mul, Ideal.map_pow]
        exact Ideal.pow_right_mono (hbound q) n
      exact hpow hmem


end AdicCompletion
