/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Algebra.Regular.SMul
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# A nonzerodivisor in the maximal ideal

If the maximal ideal of a Noetherian local ring is not an associated prime of a finite module
`M`, then it contains a nonzerodivisor on `M`.

## Implementation details

The associated primes are finite and properly contained in the maximal ideal, so prime avoidance
gives an element of the maximal ideal outside their union, which is the set of zero divisors.

## References

* [Stacks, Tag 00LL]
-/

@[expose] public section

universe u v

/-- Let `R` be a Noetherian local ring and `M` a finite `R`-module. If the maximal ideal is not
an associated prime of `M`, then it contains an element acting injectively on `M`. -/
theorem exists_mem_maximalIdeal_smul_injective
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular M x := by
  classical
  by_contra! hn
  obtain ⟨p, hp, hmp⟩ :=
    (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) (f := id) ⊥ ⊥
      (fun _ hp _ _ ↦ hp.isPrime)).mp (show
        (IsLocalRing.maximalIdeal R : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, (p : Set R) by
      rw [biUnion_associatedPrimes_eq_compl_regular R M]
      exact hn)
  exact h ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hp.isPrime.ne_top hmp ▸ hp)
