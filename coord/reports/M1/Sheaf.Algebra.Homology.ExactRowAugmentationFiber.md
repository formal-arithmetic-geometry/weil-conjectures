## What changed

Filled `CochainComplex.ExactRowAugmentation.exactRowAugmentationFiber` using proved
private helpers in the item module. The cone projections give the three coordinate
isomorphisms and support; the cone differential formulas give the signs d and -q.
The inclusion is constructed componentwise from a and the inverse coordinate map.
Its quasi-isomorphism follows from the kernel universal property in degree -1,
exactness in degree 0, epimorphicity in degree 1, and zero terms elsewhere.
Strict cone maps give the coordinate identities. Cancelling the degree -1 coordinate
proves chain-map naturality; applying the localization functor gives derived naturality.
Existing public statements, definitions, imports, and universes are unchanged.

## Proved and sorry left

Closed the one hole in
`CochainComplex.ExactRowAugmentation.exactRowAugmentationFiber`.
No holes added or split off. No sorry remains in the item module.
All private helpers are proved, and the inclusion is an explicit construction.

## No longer needed

None. The proof follows all four steps of
`lem-sp-exact-row-augmentation-fiber` and keeps both declared proof dependencies.
No imports, nodes, modules, or tool approvals were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The general Mathlib cone and short-complex
APIs suffice; no new dependency statements or changes to the unit route are required.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
