## What changed

Completed scalar-composition and arbitrary-pullback-composition coherence using a generic
mate-pasting calculation and the identity-on-sections direct-image comparisons. The retained
proofs compile against the current build. Work on the remaining two clauses continues.

## Proved and sorry left

Closed two of the four original holes:
`AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars.scalar_composition` and
`AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars.pull_composition`.
No holes added. Two remain in the item module:
`AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars.openResMap_isIso` and
`AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars.exchange_restrictScalars`, both
attached to `lem-cbc-finite-open-exchange-scalars`.

## No longer needed

None currently. The existing imports and dependency route are retained.

## Where the brief, the DAG or earlier work was wrong

The previous service failures are no longer reproducible: the compiler responded and
identified a local associativity/map-identity rewriting issue, now fixed and compiled.
No mathematical statement has changed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
