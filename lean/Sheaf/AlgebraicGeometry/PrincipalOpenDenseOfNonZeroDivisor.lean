/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Density of a principal open defined by a nonzerodivisor

Source: Stacks Project, Divisors, Lemma 31.14.4 (Tag 07ZU), affine-local calculation
(blueprint: lem-pc-principal-open-dense-of-nonzerodivisor).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- A principal open defined by a nonzerodivisor is dense in the prime spectrum.

Source: Stacks Project, Divisors, Lemma 31.14.4 (Tag 07ZU), affine-local calculation
(blueprint: lem-pc-principal-open-dense-of-nonzerodivisor).

Proof: Localization at `a` identifies its prime spectrum with `D(a)`
([lem-weil-pbc-spec-localization-away-basic-open]). Its image is dense if every minimal
prime is in the image ([lem-pc-dense-range-comap-minimal-primes]). A nonzerodivisor
lies in no minimal prime ([lem-pc-minimal-prime-avoids-nonzerodivisor]), so every
minimal prime belongs to `D(a)` and hence to the localization image. -/
theorem dense_basicOpen_of_mem_nonZeroDivisors
    (A : Type u) [CommRing A] (a : A) (ha : a ∈ nonZeroDivisors A) :
    Dense (↑(basicOpen a) : Set (PrimeSpectrum A)) := by
  sorry

end PrimeSpectrum
