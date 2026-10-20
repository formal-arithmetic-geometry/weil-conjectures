## What changed

Restored `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists` from the
current quarantine source named by `coord/rework.tsv`, then promoted its existing
`WeilConjectures.AlgebraicGeometry.CoherentFormalModule` import to `public import`.
The import now precedes the private proof imports. This exposes the definitions
needed by the existing public theorem signature. All declarations, signatures,
docstrings, proof bodies and DAG dependencies are unchanged.

This repairs the return for delivery head `c6958b233b`, based on `6488bba00`.
The current shared tree again has no active item file. I copied the current
quarantine source afresh, reproduced its unknown public `Scheme` and
`IsNoetherian` errors at line 71, and reapplied the import correction to that
source. The delivery tool packages the repair on its freshly fetched base.

The repaired item and its unchanged quarantined parent
`Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy` were compiled together in
import order. The parent was present only for validation and is not delivered.

Change record:
`coord/changes/J6-GrothendieckExistenceEasyFromExists-public-import.md`.

## Proved and sorry left

This is the public-interface compilation repair assigned by the current rework
queue. Holes closed: 0 of 1. Holes added: 0 relative to the current quarantine
source. No statements were split off.

The existing theorem `AlgebraicGeometry.grothendieckExistenceEasy_exists_from`
remains `sorry`, with node
`lem-weil-pbc-grothendieck-existence-easy-from-exists`. Its source and complete
proof in words remain in its docstring. No other declaration changes.

## No longer needed

None. No dependency, node, module or unit-route step was pruned. The private
import was promoted, preserving the dependency graph.

## Where the brief, the DAG or earlier work was wrong

The latest return asks to reapply the repair to the current source after a
concurrent landing. The current rework row still assigns restoration of
`quarantine/Sheaf/AlgebraicGeometry/GrothendieckExistenceEasyFromExists.lean`;
its absence from the active tree does not withdraw the theorem or its route.
The current source reproduces the public-import defect, which this packet
repairs without changing the mathematics.

The parent `GrothendieckExistenceEasy` remains quarantined and continues to
use this theorem. Its unchanged source was checked against this repair.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
