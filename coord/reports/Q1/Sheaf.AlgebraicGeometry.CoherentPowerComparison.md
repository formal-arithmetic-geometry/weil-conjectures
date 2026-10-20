## What changed

Restored `lean/Sheaf/AlgebraicGeometry/CoherentPowerComparison.lean` from the
quarantine path recorded in `coord/rework.tsv`. Removed its private import of
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`.
That import transitively loaded the upstream resolution-naturality declarations,
which collide with the already loaded Sheaf resolution-naturality declarations
from the canonical comparison's public interface. The import was unused by the
archived theorem body. The restored module compiles through `lcompile.py`.

This is the assigned post-sync compilation repair. No declaration, signature,
public import, definition, proof body, or DAG attachment changes.

## Proved and sorry left

Holes closed: none. Holes added: none. The existing single hole remains in
`AlgebraicGeometry.Scheme.Modules.coherentPowerComparison`
(node `new-coherent-power-comparison`). Actual module hole count: 1 before and
1 after. This delivery repairs compilation; it does not claim a mathematical
proof or a decomposition.

## No longer needed

Removed the unused private import
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`
from this restored module. No mathematical node or module is claimed pruned:
the existing proof plan and all its dependencies remain attached to
`new-coherent-power-comparison`, including the resolution-normalization node.
No quarantined file is withdrawn or listed for deletion.

## Where the brief, the DAG or earlier work was wrong

The post-sync archived import list combined two modules declaring the same
public constants. `coord/rework.tsv` records the resulting duplicate
`ExtEdgeResolution.moduleComparisonEquiv` error. Removing the unused private
normalization import avoids loading the second copy. The item statement and
its DAG attachment are preserved verbatim.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
