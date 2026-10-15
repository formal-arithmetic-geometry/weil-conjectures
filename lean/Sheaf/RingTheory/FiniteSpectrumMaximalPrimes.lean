/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Basic

import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Maximality of primes in a finite-spectrum finite-type field algebra

Source: Stacks Project, Algebra, Lemma 10.61.3 (Tag 0ALW), implication (2) to (1)
(blueprint: lem-pqf-finite-spectrum-maximal-primes).
-/

@[expose] public section

universe u v

namespace Ideal

/-- Every prime ideal in a finite-type algebra over a field with finite spectrum is maximal.
The zero ring is allowed: its spectrum is empty and the conclusion is vacuous.
Source: Stacks Project, Algebra, Lemma 10.61.3 (Tag 0ALW), implication (2) to (1)
(blueprint: lem-pqf-finite-spectrum-maximal-primes).

Proof: By finite type over the field and finiteness of the whole prime spectrum, every
fiber of `PrimeSpectrum B → PrimeSpectrum k` is finite. The Mathlib characterization
`Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` therefore gives
`Algebra.QuasiFinite k B`. The source field has discrete prime spectrum, so
`Algebra.QuasiFinite.discreteTopology_primeSpectrum` makes `PrimeSpectrum B` discrete.
Mathlib's `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero` then yields
`Ring.KrullDimLE 0 B`, and `Ring.krullDimLE_zero_iff` says exactly that every prime ideal
of `B` is maximal. This also covers the zero ring, whose spectrum is empty.
-/
theorem isMaximal_of_finite_primeSpectrum_of_finiteType
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (hfin : Finite (PrimeSpectrum B))
    (p : Ideal B) (hp : p.IsPrime) : p.IsMaximal := by
  have hq : Algebra.QuasiFinite k B := by
    rw [Algebra.QuasiFinite.iff_finite_comap_preimage_singleton]
    intro x
    apply Set.Finite.subset (Set.toFinite (Set.univ : Set (PrimeSpectrum B)))
    intro y hy
    exact Set.mem_univ y
  let _ : Algebra.QuasiFinite k B := hq
  have hdisc : DiscreteTopology (PrimeSpectrum B) :=
    Algebra.QuasiFinite.discreteTopology_primeSpectrum k B
  have hdim : Ring.KrullDimLE 0 B :=
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp hdisc).2
  exact Ring.krullDimLE_zero_iff.mp hdim p hp

end Ideal
