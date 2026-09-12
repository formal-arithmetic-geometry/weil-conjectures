/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# The dimension of a quotient by a prime is a coheight

## Main results

* `ringKrullDim_quotient_eq_coheight`: for a prime `p` of a commutative ring `R`, the Krull
  dimension of `R ⧸ p` is the coheight of `p` in `PrimeSpectrum R`.
-/

@[expose] public section

/-- The Krull dimension of `R ⧸ p`, for a prime ideal `p`, is the coheight of `p` in the prime
spectrum of `R`: the primes of `R ⧸ p` are the primes of `R` containing `p`. -/
theorem ringKrullDim_quotient_eq_coheight {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ringKrullDim (R ⧸ p) = Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) := by
  have hset : PrimeSpectrum.zeroLocus (R := R) (p : Set R)
      = Set.Ici (⟨p, hp⟩ : PrimeSpectrum R) := by
    ext x
    simp [← PrimeSpectrum.asIdeal_le_asIdeal]
  rw [ringKrullDim_quotient, hset, ← Order.coheight_eq_krullDim_Ici]
