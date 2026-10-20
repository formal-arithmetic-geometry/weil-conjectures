## What changed

Restored `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` from the archive
specified by `coord/rework.tsv`. Removed its private import of
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`.
That import pulls in the upstream naturality module, colliding with the existing
`Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality` already required
by the canonical comparison interface. The recorded global error names
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv`.

The restored file differs from the archive by precisely that one import line.
The public imports, theorem signature, docstring, body and DAG attachment are
preserved. The server compiler accepts the restored module in 5.8 seconds.

Change record:
`coord/changes/J1-qcoherent-normalized-comparison-import-repair.md`.

The sole direct importer, the quarantined
`Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback`, also imports
`Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare`. The latter is a
separate rework root held by J2. It is absent from the published library, so the
pullback consumer cannot yet be compiled and restored from this packet.
No consumer statement needs adaptation to this private-import repair.

## Proved and sorry left

This delivery repairs the listed rework failure. Holes closed: zero. Holes added:
zero. No theorem proof is claimed and no theorem is split off.

The sole existing hole remains:
`AlgebraicGeometry.Scheme.Modules.exists_unique_qcoherentNormalizedComparison`,
node `lem-weil-pbc-qcoherent-normalized-comparison-exists`.
Its source and complete natural-language proof remain in the original docstring.

## No longer needed

Removed the unused, conflicting private import
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`.
This is an import repair, not a mathematical pruning claim: its normalization
node remains in the planned proof dependencies of the unfinished theorem.
No module or DAG node is withdrawn, and no source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The upstream sync introduced a second module containing names already defined
by the existing Sheaf naturality module. Importing both naturality environments
through the archived item's imports fails before elaborating its theorem.
The unused normalization proof import was therefore not harmless scaffolding.

The current rework queue explicitly prioritizes restoration of quarantined
modules, including modules whose theorem proofs still contain holes. The repair
preserves that unfinished mathematical work and its dependencies. Generic
delta-functor proof experiments were not included in this restoration packet.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
