/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Equations of a global complete intersection at a prime

Source: Stacks Project, Algebra, proofs of Lemmas 10.135.3 and 10.135.4 (Tags 00SB, 00SC)
(blueprint: lem-weil-pbc-global-complete-intersection-local-regular-sequence).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- (blueprint: lem-weil-pbc-global-complete-intersection-local-regular-sequence)
Stacks Project, Algebra, proof of Tag 00SB and the last paragraph of the proof of Tag 00SC.
For a nonzero quotient of an `m`-variable polynomial ring by `t` equations of dimension
`m - t`, the equations form a regular sequence after localization at any prime containing
these equations. The dimension hypothesis is written additively, avoiding truncated
subtraction when `t > m`.

Proof (the six steps of the node):
1. Choose a maximal ideal containing the given prime and localize there. All equations
lie in the maximal ideal of this local ring (`def-weil-pbc-localization-at-prime`).
2. This is a regular local ring of dimension `m`, by
`lem-weil-pbc-polynomial-ring-field-regular-ring` and
`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`. Its maximal ideal has a
regular sequence of `m` generators by `lem-weil-pbc-regular-local-generators-regular-sequence`,
so its depth is at least `m` (`def-weil-pbc-depth`).
3. Apply `lem-weil-pbc-noetherian-height-quotient-bound` to the `t` equations: the local
quotient has dimension at least `m - t` (`def-weil-pbc-krull-dimension-ring`).
4. Lift chains of primes of the local quotient to the global quotient via
`lem-weil-pbc-localization-prime-residue-field-iso`. Thus its dimension is at most the
global dimension `m - t` (`def-kun-topological-krull-dimension`), giving equality.
5. Apply `lem-weil-pbc-cm-local-dimension-drop-regular-sequence` to obtain regularity at
this maximal ideal (`def-weil-pbc-regular-sequence`).
6. Localize further at the given prime using
`lem-weil-pbc-weakly-regular-sequence-localization-prime`; identify this iterated
localization with the original localization using
`lem-weil-pbc-localization-prime-residue-field-iso`. The isomorphism preserves the
successive quotients and multiplication maps, hence regularity. This final passage from
a maximal ideal to the given prime is the node's elaboration of Tag 00SC. -/
theorem isRegular_localizationAtPrime_of_quotient_dimension
    (k : Type u) [Field k] (m t : ℕ) (f : Fin t → MvPolynomial (Fin m) k)
    [Nontrivial (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f))]
    (hdim : topologicalKrullDim
      (AlgebraicGeometry.Spec
        (CommRingCat.of (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)))) +
      (t : WithBot ℕ∞) = (m : WithBot ℕ∞))
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : Ideal.span (Set.range f) ≤ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      ((List.ofFn f).map (algebraMap (MvPolynomial (Fin m) k) (Localization.AtPrime q))) := by
  sorry

end MvPolynomial
