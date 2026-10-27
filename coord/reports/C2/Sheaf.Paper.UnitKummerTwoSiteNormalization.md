## What changed

Filled `AlgebraicGeometry.Scheme.UnitKummer.proInsertion_existsUnique` with the
scalar-extension adjunction construction and its sectionwise uniqueness proof. The
module now uses explicit named coefficient-sheaf definitions and the existing
`mapExtComp`/relative-Kummer interfaces so the file elaborates within the file gate.
The target statements are unchanged. The definition repairs are recorded in
`coord/changes/`.

## Proved and sorry left

Closed one original hole:

- `AlgebraicGeometry.Scheme.UnitKummer.proInsertion_existsUnique`.

Two original holes remain, with no new holes added:

- `AlgebraicGeometry.Scheme.UnitKummer.normalization`.
- `AlgebraicGeometry.Scheme.UnitKummer.frame_normalization`.

The module compiles successfully in 35.3 seconds with these two existing `sorry`s.

## No longer needed

The proof and current declarations no longer import these old direct proof modules:

- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`.
- `WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder`.
- `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
- `Sheaf.CategoryTheory.SiteCohomologyPullback`.

Their declarations remain in the library. The retained normalization holes still
need the Kummer pullback and comparison theory supplied by the current imports.

## Where the brief, the DAG or earlier work was wrong

No statement in the brief or DAG was changed. The long normalization and frame
arguments remain open; this delivery records the completed insertion construction
rather than claiming those two theorems.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
