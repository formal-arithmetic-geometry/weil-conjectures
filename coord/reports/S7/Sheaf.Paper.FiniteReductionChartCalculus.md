## What changed

Completed all three theorem proofs in `Sheaf.Paper.FiniteReductionChartCalculus`:
`finiteReductionPowerShift`, `existsUnique_finiteReductionEtaleUnitStep`, and
`existsUnique_finiteReductionTensorUnit`. The proofs normalize the integer shift,
unfold the published étale/pro-étale derived tensor definitions once, and transport the
endpoint type to the native K-flat comparison maps. Removed unused direct public imports
from the module. Construction terms and theorem statements are unchanged. Two existing generic definitions
have explicit annotations for their previously inferred return types. The public import
removals and annotations are documented in
`coord/changes/S7-finite-reduction-chart-presentations.md`; no consumer adaptation is needed.

## Proved and sorry left

Closed 3 of 3 holes: `finiteReductionPowerShift`,
`existsUnique_finiteReductionEtaleUnitStep`, and `existsUnique_finiteReductionTensorUnit`.
No `sorry`s remain in the item module and no new `sorry`s were added.

## No longer needed

The proof does not require direct imports of `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`,
`Sheaf.Paper.FourCorners`, `Sheaf.Paper.StratumScalarExtension`,
`Sheaf.Paper.SfCompactSupportRestrictionOfScalars`, `Sheaf.Paper.SmoothTrace`, or
`WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity`; their declarations are available
through the retained `PurityCompositionCoherence` import closure where needed by this file.
The sole direct consumer, `FiniteReductionRootCharts`, explicitly imports all six removed
modules, so their declarations remain available to downstream consumers. These are redundant
direct import edges; no whole module or DAG dependency node is newly pruned or required.

## Where the brief, the DAG or earlier work was wrong

The earlier retained attempt treated the published tensor endpoint as definitionally equal
to the native endpoint at the concrete module-category instance. Kernel checking timed out
on that dependent instance comparison. The corrected proof first establishes the generic
presentation equality and transports only the endpoint type, which compiles without changing
any theorem statement or construction.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
