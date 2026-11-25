/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.NonzerodivisorIfMaximalNotAssociated

/-!
# Positive depth when the maximal ideal is not associated

A finite module over a Noetherian local ring whose associated primes do not include the
maximal ideal has depth at least one.

## References

* [Stacks, Tag 00LL]
* [Stacks, Tag 00LI]
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- A finite module over a Noetherian local ring whose associated primes do not include the
maximal ideal has depth at least one. -/
theorem depth_one_of_finite_localized_module_of_no_maximal_associated
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M) :
    (1 : ℕ∞) ≤ IsLocalRing.depth (R := R) M := by
  classical
  cases subsingleton_or_nontrivial M with
  | inl hM =>
    let := hM
    unfold IsLocalRing.depth Ideal.depth
    rw [ite_eq_left (Subsingleton.elim _ _)]
    exact le_top
  | inr hM =>
    let := hM
    obtain ⟨x, hx, hreg⟩ := exists_mem_maximalIdeal_smul_injective R M h
    unfold IsLocalRing.depth Ideal.depth
    split
    · exact le_top
    · apply le_sSup
      refine ⟨[x], ?_, ?_, by simp⟩
      · apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
        · simpa using hx
        · exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff M x).mpr hreg
      · simpa using hx

end AlgebraicGeometry.Scheme
