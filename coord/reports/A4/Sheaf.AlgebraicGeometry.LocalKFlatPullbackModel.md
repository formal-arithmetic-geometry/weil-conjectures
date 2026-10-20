## What changed

Restored `lean/Sheaf/AlgebraicGeometry/LocalKFlatPullbackModel.lean` from its
quarantine copy and retained its complete proof of
`AlgebraicGeometry.derivedPullback_local_kFlat_model`. The stale public import of
the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback` was replaced by the
source-library module `WeilConjectures.AlgebraicGeometry.DerivedPullback`; the
proof-only imports are kept as private imports. The proof compiles cleanly.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.derivedPullback_local_kFlat_model`
(node `lem-sc-local-kflat-pullback-model`). Added 0 holes and split off 0
statements. The delivered module contains no `sorry`.

## No longer needed

No proof dependencies or declarations from the node's recorded plan were pruned.
The withdrawn Sheaf import was required only as a stale attachment and is replaced
by the adopted source import; no mathematical dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The quarantined module's import of `Sheaf.AlgebraicGeometry.DerivedPullback`
was no longer usable because that module is withdrawn and the source declaration
is provided by `WeilConjectures.AlgebraicGeometry.DerivedPullback`. The theorem
statement and proof route remain unchanged.

The import-interface repair is recorded in
`coord/changes/local-kflat-pullback-model-import.md`.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
