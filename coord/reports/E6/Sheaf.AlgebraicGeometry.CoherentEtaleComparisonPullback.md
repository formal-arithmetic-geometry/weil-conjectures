## What changed

Restored `Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback` to its original
library path, following its current `coord/rework.tsv` assignment and
`tools/rework.py`, rule 3. The current shared tree has the original only at
`quarantine/Sheaf/AlgebraicGeometry/CoherentEtaleComparisonPullback.lean`.

Reapplied the repair to that current quarantined source after the return at
`099ceb10b8` (delivery base `e0d550965`). This retry improves the earlier packet:
instead of removing all 17 private proof imports, it removes only the two that
transitively import the upstream resolution-comparison implementation. That
implementation collides with the retained Sheaf implementation exported by
`CanonicalCoherentEtaleComparison`. All other 15 private proof imports remain.

The current original was copied to the sandbox and compiled through `lcompile.py`:
it failed in 0.8 seconds with the duplicate declaration
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.moduleComparisonEquiv`.
The repaired file compiled through the same service in 2.3 seconds without errors
or warnings. A textual check verifies that all three public imports and all
non-import text, including the complete theorem, match the current original.

Change record: `coord/changes/E6-coherent-etale-pullback-rework.md`.
No definition, theorem signature, source-library file or DAG attachment changes.
The quarantined consumer `CoherentFrobeniusComparison` applies the unchanged
signature; no consumer adaptation is needed. Its restoration is a separate item.

## Proved and sorry left

Assigned compile repair completed. Holes closed: zero of one; holes added: zero;
split off: zero. This is a compile repair, not a mathematical proof or decomposition.
The one remaining hole is
`AlgebraicGeometry.Scheme.Modules.coherentEtaleComparison_pullback`
(node `new-coherent-etale-comparison-pullback`). Its source and complete proof plan
remain unchanged in its docstring and DAG node. No other hole is introduced.

## No longer needed

Removed only these incompatible private imports from the restored module:

- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`

Each transitively imports
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`,
which duplicates the comparison declaration already exported through the canonical
comparison's Sheaf implementation. Neither import is used by the current theorem
body. The other 15 private imports are preserved from the current original.
No node or module is claimed globally unnecessary. The pending mathematical proof
route, its proof dependencies and the blueprint unit are unchanged; these two
imports cannot be reintroduced until the duplicate implementations are reconciled.

## Where the brief, the DAG or earlier work was wrong

This is a currently listed quarantine compile repair, rather than a fresh proof
assignment. The current rework rule requires restoring a compiling copy at its
original path. It does not authorize deleting the quarantine archive or withdrawing
the theorem. Neither action is included.

The return at `099ceb10b8` reported a concurrent change after base `e0d550965`.
For this retry the current active path was checked again and is absent; the
quarantine row, source and E6 claim remain present. The current original was used
to reproduce the failure and construct the narrower two-import repair, rather than
resubmitting the earlier 17-import removal. The delivery tools rebuild the packet
on their current fetched base. The DAG attachment and theorem statement are
preserved exactly.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
