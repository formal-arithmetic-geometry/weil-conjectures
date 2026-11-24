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

A finite map of commutative rings is of finite type and quasi-finite at every prime.

## References

* Stacks Project, Algebra, Tags 00PM and 0H8X.
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite map of commutative rings is of finite type and quasi-finite at every prime, in
the isolated-fibre-point sense of Stacks Project, Algebra, Tags 00PL, 00PM and 0H8X. -/
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
