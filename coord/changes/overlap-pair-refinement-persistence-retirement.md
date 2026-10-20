# AlgebraicGeometry.overlap_pair_map_refinement_persistence

## Reason

Retire the duplicate Sheaf module in favour of the adopted upstream module, as
assigned by `coord/retire-items.tsv` and the approved duplicate-retirement process.
The upstream theorem has the same public signature and statement, while the Sheaf
copy is already complete. The Sheaf copy has no remaining Lean importers after the
transport duplicate was withdrawn.

## Old

`lean/Sheaf/AlgebraicGeometry/OverlapPairRefinementPersistence.lean`, declaring
`AlgebraicGeometry.overlap_pair_map_refinement_persistence` with the statement
recorded in `dag/nodes/sec-picard-framework/lem-pc-fp-overlap-pair-refinement-persistence.json`.

## New

The Sheaf module is withdrawn through `deleted.txt`. The DAG node points to the
unchanged declaration in
`lean/WeilConjectures/AlgebraicGeometry/OverlapPairRefinementPersistence.lean`.
No upstream declaration, target statement, or public interface is changed.

## Users

There are no remaining Lean importers of the Sheaf copy. The empty withdrawn
`Sheaf.AlgebraicGeometry.OverlapPairSquareChartTransport` is not a live consumer;
the finite-presentation consumer is the upstream module and imports the upstream
persistence theorem directly.

| module | group holding it | effect |
| --- | --- | --- |
| none | — | No adaptation required; the source twin is already used. |

## Status

landed 20261020T162307-L-3587565 2026-10-20 (merge of deliver/H3/Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence)
