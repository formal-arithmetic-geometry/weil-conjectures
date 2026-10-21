## What changed

Restored `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre`
from its quarantine assignment as a compatibility interface for
`WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre`.
All five original public imports are retained; the source precomparison module
is added as a public import. This restores the original public theorem name,
its concrete counit normalization and all existing mathematical dependencies.
The quarantine archive and every source-library file remain untouched.

The entire archived `AlgebraicGeometry.affineTildeTensorSourcePrecomparison`
statement and proof match the adopted declaration after substituting the
already definitionally equal tilde abbreviation and renaming the unused
`let H` binder to `_H`. This reuses the existing proof rather than restating
or splitting an obligation. The node's K-flat-resolution and counit-naturality
route and the unit's realization are unchanged, so no DAG modification is needed.

Change record:
`coord/changes/V5-affine-tilde-source-precomparison-rework.md`.

## Proved and sorry left

This is a zero-hole quarantine repair. The archived module contains zero
`sorry`s; the restored module contains zero. Holes closed: none (0).
Holes added: none (0). Split off: none (0). No theorem is left with `sorry`.
The already proved `AlgebraicGeometry.affineTildeTensorSourcePrecomparison`
is re-exported from the adopted source implementation.

Validation: the compatibility module compiles on the server (0.1 seconds). A separate
consumer check restates the archived theorem's exact type with the legacy
`affineTildeFunctor` spelling and applies the source theorem (10.1 seconds). Its two
archive-style lint warnings concern the unused `let H` binder and the scratch
heartbeat option; the delivered interface compiles without warnings. The axiom check
for the source theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`. The import-direction check permits the source import.

## No longer needed

No imports, nodes, or dependency modules are removed. No module is withdrawn.
The duplicate local implementation in the restored Sheaf module is unnecessary:
the source supplies the same theorem and the same comparison maps. The eight
local elaboration-instance declarations and the archived option and local
irreducibility commands need not be repeated in the compatibility interface.
All original public imports and mathematical proof dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

The assigned item has zero proof holes: it is a quarantined restoration after
an upstream synchronization. Its absence from `lean/` does not authorize
withdrawal. The exact theorem is already proved in the adopted source tree,
and the W2 prebase repair already consolidated its data dependencies there.
Reusing that implementation is the shortest route and avoids a second copy
of the same public declaration. No new mathematical statement is required.
The existing node attachment to the final source-comparison theorem remains
unchanged; this module implements an internal step of that proof.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
