/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Associated primes defined by element annihilators

We define the associated primes of a module over an arbitrary commutative ring as the prime
ideals that are annihilators of single elements, with no radical and no Noetherian hypothesis.

## References

* Stacks Project, Algebra, Definition 00LA.
-/

@[expose] public section

universe u v

namespace RingTheory

/-- The associated primes of an `R`-module `M`: the prime ideals of `R` that are equal to
the annihilator `{a | a • z = 0}` of some element `z : M`. -/
def annihilatorAssociatedPrimes (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Set (Ideal R) :=
  {q | q.IsPrime ∧ ∃ z : M, q = (⊥ : Submodule R M).colon {z}}

end RingTheory
