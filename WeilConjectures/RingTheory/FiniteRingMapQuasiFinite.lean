/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Finite ring maps are quasi-finite at every prime

A finite ring map is of finite type and quasi-finite at every prime.

## Main results

* `Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite`

## Implementation details

The fibre ring over a prime of `R` is finite over the residue field, so its spectrum is finite
and discrete. The finite-type witness in the conclusion supplies the instance required by the
definition of `Algebra.IsQuasiFiniteAtPrime`.

## References

* [Stacks, Tag 00PL]
* [Stacks, Tag 00PM]
* [Stacks, Tag 0H8X]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite map of commutative rings is of finite type and quasi-finite at every prime, in
the sense that every point is isolated in its fibre. -/
theorem finiteType_and_isQuasiFiniteAtPrime_of_finite
    (R : Type u) (T : Type v) [CommRing R] [CommRing T] [Algebra R T]
    [Module.Finite R T] :
    ∃ hft : Algebra.FiniteType R T,
      letI := hft
      ∀ q : PrimeSpectrum T, Algebra.IsQuasiFiniteAtPrime R T q := by
  refine ⟨inferInstance, ?_⟩
  intro q
  unfold IsQuasiFiniteAtPrime
  exact isOpen_discrete _

end Algebra
