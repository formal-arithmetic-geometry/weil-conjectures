/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Quasi-finiteness along a four-ring square

Source: Stacks Project, Algebra, Lemma 10.122.7 (Tag 00PN)
(blueprint: lem-weil-pbc-quasi-finite-four-rings).
-/

@[expose] public section

universe u v w z

open scoped BigOperators

namespace Algebra

/-- (blueprint: lem-weil-pbc-quasi-finite-four-rings) In a commutative square of rings,
given by scalar towers `R → S → S'` and `R → R' → S'`, if `S` is of finite type over `R`
and every element of `S'` is a finite sum of products of images from `S` and `R'`, then
`S'` is of finite type over `R'`. Quasi-finiteness at the contraction of a prime of `S'`
passes to that prime (Stacks Project, Tag 00PN).

Proof following the eight steps of the node:
1. Images of finite algebra generators of `S` generate `S'`, by the finite-sum hypothesis
and commutativity. Contraction of primes is compatible with the square.
2. The residue-field map and the tensor pushout universal property
(`lem-weil-pbc-algebra-tensor-pushout-universal-property`) give a semilinear map of fibre rings.
3. The target fibre is spanned over its residue field by images from the source fibre,
by expanding the finite sums and balancing tensors.
4. The fibre-prime bijection (`lem-weil-pbc-fibre-ring-primes-bijection`) identifies the
contraction of the target fibre prime with the source fibre prime.
5. The isolated source prime is maximal
(`lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite`) and hence clopen.
The clopen-idempotent lemma (`lem-weil-pbc-spec-clopen-idempotent`)
provides an idempotent cutting it out.
6. The quotient by one minus that idempotent has one prime, by
`lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`, and is finite-dimensional by
`lem-weil-pbc-finite-type-algebra-dim-zero-finite`. Multiplying lifts of a spanning family
by the idempotent spans the corresponding factor.
7. The image idempotent avoids the target fibre prime. Semilinearity and step 3 show that
the target quotient by one minus this idempotent is finite-dimensional.
8. Its spectrum is finite discrete (`lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`).
The quotient-spectrum homeomorphism identifies it with an open subset of the target fibre
containing the target prime. That prime is therefore isolated, as required. -/
theorem finiteType_and_isQuasiFiniteAtPrime_of_four_rings
    (R : Type u) (S : Type v) (R' : Type w) (S' : Type z)
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S'] [Algebra.FiniteType R S]
    (hgen : ∀ x : S', ∃ (n : ℕ) (s : Fin n → S) (r : Fin n → R'),
      x = ∑ i : Fin n, algebraMap S S' (s i) * algebraMap R' S' (r i)) :
    ∃ hft : Algebra.FiniteType R' S', ∀ q' : PrimeSpectrum S',
      IsQuasiFiniteAtPrime R S (q'.comap (algebraMap S S')) →
        @IsQuasiFiniteAtPrime R' S' _ _ _ hft q' := by
  sorry

end Algebra
