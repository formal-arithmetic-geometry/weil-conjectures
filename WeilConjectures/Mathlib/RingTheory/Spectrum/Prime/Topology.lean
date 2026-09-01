/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Complements on the topology of the prime spectrum

`PrimeSpectrum.exists_specializes_of_mem_closure_range_comap`: a prime in the closure of
the range of `PrimeSpectrum.comap f` is a specialization of a prime in that range. This is
the statement about prime spectra underlying Stacks Project Tag 02JQ, whose scheme-theoretic
form is `AlgebraicGeometry.exists_specializes_of_mem_closure_range`.

`PrimeSpectrum.mem_genericPoints_iff`: the generic points of the irreducible components of
`Spec R` are the minimal primes of `R`.
-/

@[expose] public section

namespace PrimeSpectrum

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- A prime in the closure of the range of `PrimeSpectrum.comap f` is a specialization of a
prime in the range: the closure of the range is the zero locus of `RingHom.ker f`, and a
prime containing `RingHom.ker f` is the contraction of some prime of `S` up to
specialization (Stacks Project Tag 00FK). -/
@[stacks 02JQ]
theorem exists_specializes_of_mem_closure_range_comap (f : R →+* S) {z : PrimeSpectrum R}
    (hz : z ∈ closure (Set.range (comap f))) : ∃ q : PrimeSpectrum S, comap f q ⤳ z := by
  rw [closure_range_comap, mem_zeroLocus, SetLike.coe_subset_coe] at hz
  obtain ⟨q, -, hq, hle⟩ := z.asIdeal.exists_ideal_comap_le_prime (f := f) ⊥
    (by rwa [← RingHom.ker_eq_comap_bot])
  exact ⟨⟨q, hq⟩, (le_iff_specializes _ z).mp hle⟩

/-- A point of `Spec R` is the generic point of an irreducible component if and only if the
corresponding prime ideal is a minimal prime of `R`. -/
@[stacks 00ES]
theorem mem_genericPoints_iff {p : PrimeSpectrum R} :
    p ∈ genericPoints (PrimeSpectrum R) ↔ p.asIdeal ∈ minimalPrimes R := by
  change closure ({p} : Set (PrimeSpectrum R)) ∈ irreducibleComponents (PrimeSpectrum R) ↔ _
  rw [closure_singleton, zeroLocus_ideal_mem_irreducibleComponents, p.2.radical]

end PrimeSpectrum
