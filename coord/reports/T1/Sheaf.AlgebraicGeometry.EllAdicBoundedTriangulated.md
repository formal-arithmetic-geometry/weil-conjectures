## What changed

Repaired the proof of
`AlgebraicGeometry.ProEtale.CondensedRing.isTriangulated_boundedConstructible_ellAdic`
in `Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated`.
Case analysis on `IsEllAdicFinitenessCoefficient` exposes `Fact ℓ.Prime` and the field
or integral presentation. Each case applies the existing proved upstream instance
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible`.
The unit-ball case explicitly supplies `IsFinitenessCoefficient.unitBall`.
The theorem signature, definitions, attributes and all public imports are unchanged.

The server single-file compile passed cleanly. A standalone consumer importing only
the repaired module also compiled after opening the same lax/oplax monoidal scopes
used by the original module. Its axiom check reports exactly `propext`,
`Classical.choice` and `Quot.sound`. The proof follows the existing node
`lem-sfb-dc-ell-adic-triangulated` and its existing dependency
`lem-sfb-bounded-constructible-triangulated-finiteness`; no route change is needed.
Searches through msearch.py (LeanFinder, Loogle and grep) and direct source searches
confirmed that the existing source theorem provides the complete specialization.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.isTriangulated_boundedConstructible_ellAdic`
(node `lem-sfb-dc-ell-adic-triangulated`).
No holes remain in the item. No holes were added and no results were split off.

## No longer needed

None. No imports, nodes or modules are pruned. The existing public imports are
preserved as part of the exported interface. The proof needs only the already
imported upstream finiteness-coefficient theorem and its coefficient constructors.

## Where the brief, the DAG or earlier work was wrong

The upstream synchronization replaced the finiteness-coefficient theorem name
used by the previous proof. The generic
`isTriangulated_boundedConstructible_of_serre` takes a ring and three heart-closure
instances, and has no `ℓ` parameter. The coefficient specialization is now named
`AlgebraicGeometry.ProEtale.isTriangulated_boundedConstructible`.
The repair applies that specialization instead of duplicating the Serre proof.

The dependency node `lem-sfb-bounded-constructible-triangulated-finiteness` still
records `isTriangulated_boundedConstructible_of_serre` in its `lean.declaration`,
although its recorded signature, mathematical statement and current source all
identify `isTriangulated_boundedConstructible`. This stale name is reported for
maintainer reconciliation; the current item's node and dependency route already
match the repaired proof.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
