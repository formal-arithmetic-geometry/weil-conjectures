/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Quasi-compactness of the complement of a finitely generated vanishing locus

The complement of `V(I)` in the prime spectrum is quasi-compact for a finitely
generated ideal `I`, being the finite union of the basic opens at the generators.
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

/-- **Quasi-compactness of the complement of a finitely generated vanishing locus**
(blueprint §2.4): the complement of `V(I)` in the prime spectrum of `R` is
quasi-compact for a finitely generated ideal `I`, being the finite union of the basic
opens at the generators. -/
theorem Ideal.FG.isCompact_compl_zeroLocus {I : Ideal R} (hI : I.FG) :
    IsCompact (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := by
  obtain ⟨s, rfl⟩ := hI
  have h1 : (PrimeSpectrum.zeroLocus ((Ideal.span (s : Set R) : Ideal R) : Set R))ᶜ =
      ⋃ f ∈ s, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    ext x
    simp [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  rw [h1]
  exact s.finite_toSet.isCompact_biUnion fun f _ ↦ PrimeSpectrum.isCompact_basicOpen f

