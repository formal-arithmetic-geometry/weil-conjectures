/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Finite-type algebras with finite spectrum

A finite-type algebra over a field with finite prime spectrum is finite-dimensional, has
discrete spectrum, and all its primes are maximal.

## References

* [Stacks, Tag 00KH]
* [Stacks, Tag 0ALW]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite-type algebra over a field with finite prime spectrum is finite-dimensional,
with discrete spectrum and only maximal prime ideals. -/
theorem finiteType_finiteSpectrum
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (hfin : Finite (PrimeSpectrum B)) :
    (∀ p : PrimeSpectrum B, p.asIdeal.IsMaximal) ∧ Module.Finite k B ∧
      DiscreteTopology (PrimeSpectrum B) := by
  have : Finite (PrimeSpectrum B) := hfin
  -- A finite Jacobson spectrum is discrete, so no separate maximality lemma is needed.
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hdisc : DiscreteTopology (PrimeSpectrum B) := inferInstance
  have hdim : Ring.KrullDimLE 0 B :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
  have hfinite : Module.Finite k B :=
    (Module.finite_iff_krullDimLE_zero (R := k) (A := B)).2 hdim
  exact ⟨fun p ↦ (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).1
    isClosed_singleton, hfinite, hdisc⟩

end Algebra
