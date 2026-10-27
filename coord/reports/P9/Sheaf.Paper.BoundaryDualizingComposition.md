## What changed

Removed the unused proof-only import `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` from
`lean/Sheaf/Paper/BoundaryDualizingComposition.lean`. The import was the global-build failure reported
for this rework item; no declaration, signature, definition, or target statement changed.

The repaired module compiles successfully with `lcompile.py` after this removal.

## Proved and sorry left

No existing theorem was proved in this repair. The module still has the one pre-existing sorry in
`AlgebraicGeometry.Etale.boundary_dualizing_composition` (node
`lem-weil-boundary-dualizing-composition`). No new sorry was added.

## No longer needed

The removed import `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` was not referenced by
any declaration in this module and is not among the proof dependencies of either attached DAG node.

## Where the brief, the DAG or earlier work was wrong

The rework record names a stale dependency on `Sheaf.Paper.EtaleCompactScalarCoherence`, while the
current module's failing import was `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
The latter import was unused and its own dependency chain is currently unavailable, so removing it is
the minimal repair. The theorem proof remains unchanged because this assignment concerns the import
failure.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 INFRA.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.BoundaryDualizingComposition": "800425c60cfeaa13516a89ef673a8ab1d4165f53"}, "results": {"Sheaf.Paper.BoundaryFiniteSiteData": {"hash": "6f2bad4286a86c2f36ebbb773e8883804638f227", "status": "INFRA"}, "Sheaf.Paper.BoundaryFiniteTorDomains": {"hash": "64b8ffe8b9a6e09dc32193ed332ba22b4ff7847c", "status": "INFRA"}, "Sheaf.SixFunctors.FiniteDualizingData": {"hash": "85a1df7dce865940061baf88f578c68a501713c3", "status": "INFRA"}}, "seconds": 403, "time": "2026-10-27T23:42:13+0800", "transitive": 0, "version": 1}
```

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
