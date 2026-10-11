/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Weakly associated prime ideals

Source: Stacks Project, Algebra, Definition 10.66.1 (Tag 0547)
(blueprint: def-sc-weakly-associated-primes).

The annihilator of `x` is the colon ideal `(⊥ : Submodule A A).colon {x}`, and weak
association is membership in its minimal primes, as in
`Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`.
-/

universe u

namespace Ideal

/-- The weakly associated prime ideals of a commutative ring are the primes
minimal over the annihilator `(⊥ : Submodule A A).colon {x} = {a | a * x = 0}` of a
single element `x` (Stacks Project, Algebra, Definition 10.66.1, Tag 0547)
(blueprint: def-sc-weakly-associated-primes). -/
def WeakAss (A : Type u) [CommRing A] : Set (Ideal A) :=
  {p | ∃ x : A, p ∈ ((⊥ : Submodule A A).colon {x}).minimalPrimes}

end Ideal
