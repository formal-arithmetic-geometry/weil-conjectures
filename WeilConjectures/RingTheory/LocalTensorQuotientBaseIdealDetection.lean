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
import WeilConjectures.RingTheory.LocalTensorQuotientComponentMap

/-!
# Detection of tensor quotients modulo the extended base ideal

An element of `(R_p/m^n) ⊗_R S` vanishes as soon as its images in all `S_q/m^n S_q`, for primes
`q` of `S` over `p`, vanish.

## Implementation details

For `S` finite over `R`, the ring `C = B/m^n B` with `B = R_p ⊗_R S` is Artinian, hence the
product of its localizations, which are the rings `S_q/m^n S_q`. If there are no primes over
`p`, then `C` is the zero ring.

## References

* [Stacks, Tag 07N9] (quotient-product argument)
* [Stacks, Tags 00JA, 00CT]
-/

@[expose] public section

universe u v w
open scoped TensorProduct
namespace AdicCompletion

/-- Local membership in the extended base-ideal power detects a tensor quotient. -/
theorem local_tensor_quotient_base_ideal_detection
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (n : ℕ) (hn : 0 < n) :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    ∀ (ι : Type w) (t : Finset ι) (r : ι → A) (s : ι → S),
      (∀ q : p.primesOver S,
        (∑ i ∈ t, Localization.localRingHom p q.1 (algebraMap R S)
          (Ideal.LiesOver.over (P := q.1) (p := p)) (r i) *
          algebraMap S (Localization.AtPrime q.1) (s i)) ∈
            (m ^ n).map (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p)))) →
      (∑ i ∈ t, (Ideal.Quotient.mk (m ^ n) (r i)) ⊗ₜ[R] s i) = 0 := by
  dsimp
  obtain ⟨φ, hφ, hpure⟩ := tensor_quotient_component_map R S p n hn
  intro ι t r s h
  apply hφ
  ext q
  rw [map_sum φ]
  simp only [Finset.sum_apply, map_zero]
  simp_rw [hpure]
  rw [← map_sum]
  exact (Ideal.Quotient.eq_zero_iff_mem).2 (h q)

end AdicCompletion
