## What changed

Retired `Sheaf.AlgebraicGeometry.OverlapPairSquareChartTransport` in favour of
`WeilConjectures.AlgebraicGeometry.OverlapPairSquareChartTransport`, following
this item's explicit retirement assignment in `coord/retire-items.tsv`.
`deleted.txt` withdraws the duplicate; the delivery tool lands an empty module.
The sole consumer, `Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence`
(unclaimed), now privately imports the source twin and omits the redundant `hp`
argument at its theorem call. Its existing signatures and public imports are unchanged.
The private existential helper keeps its own `hp` binder and acknowledges it with
`have _ := hp`. The existing transport DAG node now points at the source theorem.
No source-library file was edited.

The original item compiled in 41.0 seconds; the adapted consumer compiled in
12.5 seconds. A separate axiom check of the source theorem compiled in 4.5 seconds
and reported only `propext`, `Classical.choice`, `Quot.sound`.
The change record is
`coord/changes/overlap-pair-square-chart-transport-retirement.md`.

## Proved and sorry left

Holes closed: 0. Holes added: 0. Holes left: 0. Nothing is split off.
Both the item and its consumer were already sorry-free when this session began.
`AlgebraicGeometry.overlap_pair_square_chart_transport` remains completely proved
by the adopted source theorem; its axiom check contains no sorry axiom.
`AlgebraicGeometry.overlap_pair_map_refinement_persistence` retains its complete
proof and exact signature. This delivery records duplicate retirement, not a new
hole closure or a decomposition.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.OverlapPairSquareChartTransport`.
Removed the consumer's proof import of that module and replaced it by the source
twin. The duplicate generic private helpers and module comparison calculation
are no longer needed in the Sheaf tree; the full unchanged proof remains upstream.
No mathematical dependency node is removed: the transport node now attaches to
its existing upstream realization. The two proof dependencies
`def-pc-local-overlap-transitions` and `def-pc-overlap-pair-canonical-comparisons`
remain needed by that proof. No new modules or nodes were introduced.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief is stale for this item: the shared module already has
zero holes, and the human's retirement table identifies the actual assigned work.
The adopted source theorem has the same explicit transported pair map and conclusion
but no `hp : p' ≫ r = p` binder. The Sheaf proof never used that binder except to
suppress an unused-variable warning. Its chart equations suffice, so the existing
source theorem directly supplies the old consumer's result. The node's original
statement and three-step proof plan remain valid; only its Lean attachment was stale.

Fresh `msearch.py` searches used Lean Finder, Loogle and grep. Loogle supplies
`pullHom_pullHom` and related identities, and the source search found the complete
upstream proof. No replacement mathematical route or unproved lemma is necessary.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
