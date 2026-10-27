## What changed

Restored `Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence` from its
quarantined source as a compatibility module publicly importing
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence`.
The unchanged archive fails because its Sheaf tensor-naturality declarations
collide with the source copies imported by the current ComparisonNaturality
compatibility module. The adopted source TotalCoherence module already defines
and proves the same API. This repair removes that actual import collision.

Preserved declarations:
- `AlgebraicGeometry.tensorResolutionChartRestrictionComplexIso`;
- `AlgebraicGeometry.tensorResolutionChartRestriction_total_inv`;
- `AlgebraicGeometry.tensorResolutionChartRestriction_total`.

The definition has the same `Functor.mapHomologicalComplexCompIso` body. Direct
applications of the adopted theorems to the complete archived theorem types
compiled in a scratch module (8.2 seconds, no warnings). The repaired module
compiled in 1.2 seconds, no warnings. All three declarations have only `propext`,
`Classical.choice`, and `Quot.sound` as axioms.

The archived HomologyCoherence consumer compiled unchanged against the repaired
module (51.5 seconds); its pre-existing unscoped-heartbeat and long-line style
warnings remain in that scratch check. Six quarantined direct consumers were
identified and their uses retain the identical names and types. No consumer
adaptations or source-library edits are needed. The six archives are preserved.

Change record: `coord/changes/F1-qcoh-total-coherence-compatibility.md`.

## Proved and sorry left

This is a zero-hole rework assignment: 0 original sorries, 0 closed, 0 added,
0 split off, 0 remaining. There are no declarations with sorry to list.
The two existing proved coherence identities and the concrete isomorphism are
re-exported from the adopted source module. This delivery repairs the import
failure; it does not claim a newly closed proof hole.

## No longer needed

Removed the three direct public Sheaf imports:
- `Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence`;
- `Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents`;
- `Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality`.

Their mathematical declarations remain supplied by the corresponding source
modules through the single adopted TotalCoherence import. Duplicate local
redeclarations are unnecessary. No mathematical proof dependency, DAG node,
unit step, or consumer is pruned. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it was quarantined after a cluster restore,
not because its mathematics was withdrawn. Its archived file has zero holes;
the queue's displayed 1 is an error/repair entry, not an actual sorry count.
Restoring the archive verbatim reproduces an import collision introduced by
mixing the kept Sheaf helper chain with adopted source compatibility imports.
The source module provides the already proved, identical coherence API.

No DAG node attaches directly to this helper module. The parent node
`new-t3-qcoh-tensor-resolution-chart-comparison-naturality` still explicitly uses
`tensorResolutionChartRestriction_total` in proof step 3; this use is preserved.
No node or unit-route update is appropriate, and no new nodes are introduced.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
