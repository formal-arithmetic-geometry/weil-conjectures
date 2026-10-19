/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.NoetherianLocalDomainInfiniteOpens

/-!
# Closed points in a punctured local spectrum

Source: Stacks Project, Morphisms Tag 02J6(4), Properties Tag 02IM(1),
and the locally closed characterization following Topology Tag 005U
(blueprint: lem-per-punctured-local-closed-points).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- Every nonempty locally closed subset of the punctured spectrum of a nonzero
Noetherian local ring contains a point closed in that punctured spectrum.

Source: Stacks Project, Morphisms Tag 02J6(4), Properties Tag 02IM(1),
and the locally closed characterization following Topology Tag 005U
(blueprint: lem-per-punctured-local-closed-points).

Proof:
1. The spectrum is T0. The zero-locus radical formula and finite generation of
ideals imply it is Noetherian, using `lem-weil-pbc-spec-irreducible-closed-subsets-primes`,
`lem-weil-pbc-zero-locus-eq-iff-radical-eq`, and `def-weil-pbc-noetherian-ring`.
2. Every subset is compact by `lem-sfb-noetherian-space-compact-subsets`. Thus the
nonempty T0 subspace W has a point w closed in W, by
`lem-sc-quasi-compact-kolmogorov-closed-point` applied to its whole space.
3. The puncture U is open: every prime is contained in the unique maximal ideal
by `lem-weil-pbc-proper-ideal-contained-in-maximal`, so that ideal has singleton
zero locus. Since W is locally closed in U and w is closed in W, its singleton
is locally closed in U and hence in the spectrum. If p is its prime, intersect
an open-closed presentation with its closure V(p); this makes {p} open in V(p).
4. If w were not closed in U, its closure in U would contain a distinct prime q,
with p strictly below q strictly below the maximal ideal. The quotient B = A/p
is a nonzero local domain by `lem-weil-pbc-quotient-local-structure`. It is
Noetherian: images of generators of inverse images generate its ideals.
5. By `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`, Spec B is homeomorphic
to V(p). The three strict primes 0, q/p, m/p give a chain of irreducible closed
subsets of length two, using `lem-weil-pbc-spec-irreducible-closed-subsets-primes`.
Thus its dimension is at least two by `def-kun-topological-krull-dimension`.
Step 3 also shows that its zero prime is an open singleton.
6. This contradicts `lem-per-noetherian-local-domain-open-infinite` (Stacks 02IG):
every nonempty open of that Noetherian local domain is infinite. Hence w is
closed in U, as required. -/
theorem exists_isClosed_singleton_of_isLocallyClosed_punctured
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (W : Set {x : AlgebraicGeometry.Spec (.of A) // x ≠ IsLocalRing.closedPoint A})
    (hWnonempty : W.Nonempty) (hWlocallyClosed : IsLocallyClosed W) :
    ∃ w ∈ W, IsClosed ({w} :
      Set {x : AlgebraicGeometry.Spec (.of A) // x ≠ IsLocalRing.closedPoint A}) := by
  sorry

end PrimeSpectrum
