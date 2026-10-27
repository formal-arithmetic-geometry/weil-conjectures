## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralTensorPullback.restrictionPullback_existsUnique`
without changing its signature or any definition. Its witness is the existing
`CondensedRing.comapUpperStarIso` for the constant-function coefficient map.
After collapsing extension along the two invertible coefficient-pullback maps,
the normalization equation is the coefficient square and monoidal naturality.
The normalization determines every component: precomposition with the displayed
generator map is injective because the extension unit factors through that map
and is invertible. Added proved private helpers for the quotient formula, the epimorphism fact,
and the generic coefficient-square argument. The public theorem specializes
that generic argument to avoid expanding geometric definitions during checking.
Added proof-only imports for the existing comparison API.

## Proved and sorry left

Closed 1 of the item's 2 holes:
`AlgebraicGeometry.ProEtale.IntegralTensorPullback.restrictionPullback_existsUnique`.
No holes added or split off.

One hole remains, unchanged:
`AlgebraicGeometry.ProEtale.IntegralTensorPullback.preserves_and_completed`
(node `det-lem-int-tensor-pullback`). The original full proof docstring and DAG
plan remain attached. All previously proved declarations retain their proofs.

## No longer needed

None. No existing imports, nodes, modules or unit steps were removed. The final
preservation/completion theorem remains open and still needs its declared route.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The canonical restriction/pullback isomorphism already
exists as `CondensedRing.comapUpperStarIso`; this delivery supplies its additional
normalization and uniqueness rather than constructing a second comparison.
The final theorem's strict-Roos dependency is expressed in sectionwise module
categories, whereas this module uses internal modules, so using it will require
explicit transport of its canonical towers and units.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
