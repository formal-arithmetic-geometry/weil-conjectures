/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Going down and surjective spectra bound Krull dimension

Source: Stacks Project, Algebra, Lemma Tag 00OH (blueprint:
lem-sc-going-down-surjective-dimension).
-/

universe u v

/--
Going down together with surjectivity on prime spectra implies the Krull-dimension
inequality.  The going-down property of `φ` (Stacks Tag 00HV (2)) is
Mathlib's `Algebra.HasGoingDown` for the algebra structure `φ.toAlgebra`.
Source: Stacks Project, Algebra, Lemma Tag 00OH
(blueprint: lem-sc-going-down-surjective-dimension).

Proof (using `def-weil-pbc-krull-dimension-ring`):
1. If `R` is the zero ring, its prime spectrum is empty and `ringKrullDim R = ⊥`,
   so the inequality is immediate. Otherwise, take any finite strict chain
   `p₀ < ⋯ < pₙ` of primes of `R`. Spectrum surjectivity supplies a prime `qₙ`
   of `S` whose contraction is `pₙ`.
2. Apply going down successively, from `pₙ₋₁ ≤ pₙ` down to `p₀ ≤ p₁`, obtaining
   primes `qᵢ ≤ qᵢ₊₁` contracting to `pᵢ`. Each inclusion is strict: equality
   would give equal contractions, contrary to the strictness of the original chain.
3. Thus every finite prime-chain length in `R` occurs in `S`. Taking suprema
   according to `ringKrullDim` gives the stated inequality, including unbounded dimension.
-/
theorem ringKrullDim_le_of_goingDown_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (hgoing : letI := φ.toAlgebra; Algebra.HasGoingDown R S)
    (hsurjective : Function.Surjective (PrimeSpectrum.comap φ)) :
    ringKrullDim R ≤ ringKrullDim S := by
  sorry
