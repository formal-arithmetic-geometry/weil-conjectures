## What changed

Restored `lean/Sheaf/AlgebraicGeometry/DiagonalPushforwardStructure.lean` from the quarantine
path recorded in `coord/rework.tsv`. Replaced the public import of the withdrawn empty
`Sheaf.AlgebraicGeometry.DerivedPullback` module with the canonical defining module
`WeilConjectures.AlgebraicGeometry.DerivedPullback`. This repairs visibility of
`derivedPullback` in the public theorem signature.

The complete theorem `AlgebraicGeometry.diagonal_counit_identity`, its proof and its
existing node `lem-sc-smooth-proper-diagonal-pushforward-structure` are preserved.
Change record: `coord/changes/G3-diagonal-pushforward-derived-pullback-import.md`.

## Proved and sorry left

This is the assigned zero-hole restoration/interface repair. The archived module has
zero sorries; the restored module has zero sorries. Holes closed: none (0 of 0).
Holes added: none. No statements were split off.

Server validation through `lcompile.py`: compiled successfully in 15.0 seconds
(exit code 0). The delivery tool runs the final preflight and axiom/sorry probe.

The existing complete proof of `AlgebraicGeometry.diagonal_counit_identity` is preserved:
compose derived direct images along the diagonal and second projection, use uniqueness
of right adjoints, and apply `diagonal_baseChange_upperShriek_local` at the structure
sheaf. Its dependency theorems remain available under their current canonical names.

## No longer needed

Removed only `public import Sheaf.AlgebraicGeometry.DerivedPullback`, an empty withdrawn
compatibility module, replacing it with the defining upstream module. No mathematical
node or module is pruned; all recorded statement and proof dependencies remain needed.
No archived consumer is withdrawn. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined after the upstream sync,
not because its mathematics was withdrawn. Its archive retained an obsolete public
import, which no longer exports `derivedPullback`; the rework row records this exact
failure. The same visibility repair has already landed for its local base-change
proof dependency. There is no theorem-statement or DAG-route correction.

Current-source downstream analysis reports no consumers, but
`quarantine/Sheaf/AlgebraicGeometry/DiagonalCounitAcrossUniverses.lean` imports the item
and applies its theorem. That consumer and the existing Lean attachment are preserved;
no adaptation is required because the theorem signature is unchanged.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
