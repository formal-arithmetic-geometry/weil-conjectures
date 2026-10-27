## What changed

Replaced the private proof dependency on
`Sheaf.Paper.CoefficientRingedSquareNormalization` by the proved upstream theorem
`Functor.rightDerivedFunctorCompMapDerivedCategoryIso_eq_viaRightDerived` from
`WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`.
The abstract `derived_square_conjugate` calculation now ends in the direct exact
composition comparison. Its concrete specialization proves conjugacy with the inverse of
`derivedComapLowerStarIso` directly by unfolding that specified construction. The public
proof therefore identifies the scalar path with the inverse pull comparison without
invoking the ringed-square normalization theorem. Updated the node's proof route.

All public signatures, definitions, public imports and exported attributes are preserved.
Only private proof imports, helper signatures and proof bodies change; no consumers require
adaptation. See `coord/changes/V8-coefficient-projection-direct-comparison.md`.

## Proved and sorry left

The current source already contains a complete proof of
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientProjectionSquare`
(node `lem-sfb-coefficient-projection-square`), landed by N1. The initial unchanged-source
server compile passed in 44.4 seconds. The present delivery claims zero holes closed out of
zero existing holes, zero holes added, and zero statements split off. No `sorry` remains in
the item module. The revised server compile passed in 52.2 seconds with no warnings.
The scalar tensor realization remains a declared dependency. Its mathematical hypotheses
and the canonical projection-mate square are retained; no invertibility of push or
projection maps is used.

## No longer needed

Removed the private import `Sheaf.Paper.CoefficientRingedSquareNormalization` and the direct
proof dependency `lem-sfb-coefficient-ringed-square-normalization`: the equality required
here follows directly from the already proved abstract exact-composition comparison.
This does not withdraw that module or its node, or claim it is globally pruned; other
consumers may still need it. The scalar realization and the unit's projection compatibility
route are retained.

## Where the brief, the DAG or earlier work was wrong

The dispatcher assigned this as a proof item with one hole, but the current shared source
already has zero holes and records N1's successful landing. There is no open V8 return,
rework row, or listed repair for this module. The queue entry is stale. The packet makes a
real dependency pruning rather than reproducing N1's delivery, and reports its zero hole
count honestly. No statement or definition repair is needed.

The proposed removal of the two section-module derived-category instance constructions was
tested and rejected: the scalar tensor realization theorem requires those instances. The
final packet retains them.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
