/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Maximality of primes in a finite-spectrum finite-type field algebra

Source: Stacks Project, Algebra, Lemma 10.61.3 (Tag 0ALW), implication (2) to (1)
(blueprint: lem-pqf-finite-spectrum-maximal-primes).
-/

universe u v

namespace Ideal

/-- Every prime ideal in a finite-type algebra over a field with finite spectrum is maximal.
The zero ring is allowed: its spectrum is empty and the conclusion is vacuous.
Source: Stacks Project, Algebra, Lemma 10.61.3 (Tag 0ALW), implication (2) to (1)
(blueprint: lem-pqf-finite-spectrum-maximal-primes).

Proof: By `lem-weil-pbc-finite-type-over-field-prime-intersection-maximal`, the algebra is
Jacobson, so a prime `p` is the intersection of the maximal ideals containing it. There are
finitely many such maximal ideals, since the spectrum is finite. This family cannot be empty:
its empty intersection would be the whole ring, whereas `p` is proper. If `p` were not
maximal, every maximal ideal `m` containing it would strictly contain it. Choose an element
of each `m` outside `p`. The finite product of these elements belongs to every such `m`,
hence to their intersection `p`. Primality then puts one factor in `p`, a contradiction.
Thus `p` is maximal. This is equivalently Krull dimension at most zero. -/
theorem isMaximal_of_finite_primeSpectrum_of_finiteType
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (hfin : Finite (PrimeSpectrum B))
    (p : Ideal B) (hp : p.IsPrime) : p.IsMaximal := by
  sorry

end Ideal
