/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Separating a closed set from the closure of an image in a prime spectrum

For a ring map `φ : R → S` and ideals `I` of `R` and `J` of `S`, we show that if the closure of
the image of `V(J)` is disjoint from `V(I)`, then some `f ∈ R` is one modulo `I` with `φ f ∈ J`.

## Implementation details

Taking `I' = J.comap φ`, whose zero locus is the closure of the image of `V(J)`, avoids the
power replacement in the original Stacks proof.

## References

* [Stacks, Tag 07M3]
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- If the closure of the image of `V(J)` under `Spec φ` is disjoint from `V(I)`, then there is
an element `f` of `R` that is one modulo `I` and satisfies `φ f ∈ J`. -/
theorem exists_one_mod_mem_of_disjoint_closure_image_zeroLocus
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (J : Ideal S)
    (h : Disjoint (closure (comap φ '' zeroLocus (J : Set S)))
      (zeroLocus (I : Set R))) :
    ∃ f : R, Ideal.Quotient.mk I f = 1 ∧ φ f ∈ J := by
  rw [closure_image_comap_zeroLocus] at h
  have hc : IsCoprime I (J.comap φ) := by
    apply Ideal.coprime_of_no_prime_ge
    intro P hIP hJP hprime
    apply Set.disjoint_left.1 h
    · exact (mem_zeroLocus ⟨P, hprime⟩ _).mpr hJP
    · exact (mem_zeroLocus ⟨P, hprime⟩ _).mpr hIP
  obtain ⟨g, hg, f, hf, hgf⟩ := hc.exists
  refine ⟨f, ?_, hf⟩
  have eq := congrArg (Ideal.Quotient.mk I) hgf
  simpa [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hg] using eq

end PrimeSpectrum
