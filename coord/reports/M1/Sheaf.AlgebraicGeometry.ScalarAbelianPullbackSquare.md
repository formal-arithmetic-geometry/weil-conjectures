## What changed

Withdraw the retired Sheaf compatibility copy. The node is attached to the adopted
`WeilConjectures.AlgebraicGeometry.ScalarAbelianPullbackSquare` module, whose source
module contains the complete declarations and proof. The withdrawn Sheaf path is
replaced by the delivery tool's empty module stub. No Lean importer refers to this
Sheaf path, and no source declaration or target statement changes.
See change record `coord/changes/M1-retire-scalar-abelian-pullback-square.md`.

## Proved and sorry left

This is a listed retirement/rework repair with zero remaining holes in the item
module. The adopted source twin already proves
`AlgebraicGeometry.Scheme.scalar_abelian_pullback_square`; the Sheaf copy declares no
independent theorem. No new `sorry` is added.

## No longer needed

The quarantined Sheaf implementation and its duplicate declarations are no longer
needed. The old implementation redeclared the scalar inverse-image, coefficient,
and pullback-square declarations already provided by the adopted
`WeilConjectures` module, which caused the recorded duplicate-environment failure.
No dependency node or source module is removed.

## Where the brief, the DAG or earlier work was wrong

The quarantined file followed the pre-sync Sheaf implementation and imported a Sheaf
scalar-factorization module while also defining declarations now supplied by the
adopted source tree. The current node and retirement record correctly identify the
WeilConjectures twin as the sole declaration source; the implementation is therefore
withdrawn rather than restored.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
