/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.PartialParametersQuotientDimension

/-!
# Infinite open subsets of a Noetherian local domain

Source: Stacks Project, Algebra, Tag 02IG,
`lemma-Noetherian-local-domain-dim-2-infinite-opens`
(blueprint: lem-per-noetherian-local-domain-open-infinite).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Every nonempty open subset of the spectrum of a Noetherian local integral domain
of topological Krull dimension at least two is infinite.

Source: Stacks Project, Algebra, Tag 02IG,
`lemma-Noetherian-local-domain-dim-2-infinite-opens`
(blueprint: lem-per-noetherian-local-domain-open-infinite).

Proof:
1. Suppose O is finite. The zero prime is generic, by the closure formula in
`lem-weil-pbc-spec-irreducible-closed-subsets-primes`, so it belongs to O.
Remove the finitely many closures of the other points of O. None contains the
zero prime, so the resulting singleton consisting of the zero prime is open.
2. By `def-weil-pbc-krull-dimension-ring` and
`lem-weil-pbc-noetherian-local-system-of-parameters`, the dimension is a finite
integer d with d >= 2. In particular, the spectrum is not a singleton.
3. The basis clause of `lem-weil-pbc-spec-localization-away-basic-open` gives
x with D(x) equal to the generic singleton. Thus x is nonzero and is not a unit,
so x belongs to the maximal ideal of the local ring.
4. The quotient R/xR is a nonzero Noetherian local ring. The nonzero element x
is a nonzerodivisor, so `lem-weil-pbc-dimension-quotient-nonzerodivisor`
gives dimension d - 1 for R/xR.
5. Apply `lem-weil-pbc-noetherian-local-system-of-parameters` to R/xR, obtaining
d - 1 elements generating an ideal whose radical is its maximal ideal, and a
power of that maximal ideal contained in the generated ideal. Lift the elements
to y_2, ..., y_d in the maximal ideal of R. Their lifts together with x generate
an ideal I whose radical is the maximal ideal: the power containment lifts,
and the reverse containment follows since all generators lie in that prime ideal.
6. Reorder the parameters as y_2, x, y_3, ..., y_d. By
`lem-per-partial-parameters-quotient-dimension`, the quotients R/(y_2) and
R/(y_2, x) have dimensions d - 1 and d - 2, respectively.
7. The first dimension equality forces y_2 to be nonzero. If every prime
containing y_2 contained x, the quotient-prime correspondence would identify
the prime chains of the two quotients, making their dimensions equal by
`def-weil-pbc-krull-dimension-ring`. Hence a prime contains y_2 but not x.
It is a nonzero point of D(x), contradicting that D(x) is the generic singleton. -/
theorem Spec.infinite_of_isOpen_of_two_le_topologicalKrullDim
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hdim : 2 ≤ topologicalKrullDim (Spec (CommRingCat.of R)))
    (O : Set (Spec (CommRingCat.of R))) (hO : IsOpen O) (hne : O.Nonempty) :
    O.Infinite := by
  sorry

end AlgebraicGeometry
