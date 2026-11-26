/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.LinearAlgebra.Pi

/-!
# Injectivity of localization at associated primes

A module over a Noetherian ring injects into the product of its localizations at its associated
primes.

## Implementation details

Mathlib's `associatedPrimes` agrees with the annihilator definition by `isAssociatedPrime_iff`.
No finite generation assumption on the module is needed.

## References

* [Stacks, Tag 0311]
-/

@[expose] public section

universe u v

namespace Module

/-- Over a Noetherian ring, the canonical linear map from a module to the product of its
localizations at associated primes is injective. Equivalently, an element killed by a
denominator outside each associated prime is zero. -/
theorem injective_pi_localization_associatedPrimes
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective
      (LinearMap.pi (fun p : associatedPrimes R M =>
        (LocalizedModule.mkLinearMap p.1.primeCompl M :
          M →ₗ[R] LocalizedModule.AtPrime p.1 M))) ∧
    (∀ m : M, (∀ p : associatedPrimes R M,
      ∃ s : R, s ∉ p.1 ∧ s • m = 0) → m = 0) := by
  have hzero : ∀ m : M,
      (∀ p : associatedPrimes R M,
        ∃ s : R, s ∉ p.1 ∧ s • m = 0) → m = 0 := by
    intro m hm
    by_contra hmn
    obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R m hmn
    obtain ⟨s, hsp, hsm⟩ := hm ⟨p, hp⟩
    have hsann : s ∈ (⊥ : Submodule R M).colon {m} := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hsm
    exact hsp (hle hsann)
  refine ⟨?_, hzero⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  intro p
  have hmap : (LocalizedModule.mkLinearMap p.1.primeCompl M :
      M →ₗ[R] LocalizedModule.AtPrime p.1 M) (x - y) = 0 := by
    have h := congr_fun hxy p
    rw [map_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨s, hs, hsm⟩ := (LocalizedModule.mem_ker_mkLinearMap_iff.mp hmap)
  exact ⟨s, hs, hsm⟩

end Module
