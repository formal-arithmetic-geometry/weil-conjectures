## What changed

Completed the queued retirement of Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts.
The sole direct consumer, Sheaf.AlgebraicGeometry.FinitePresentationLocalMapDatum, now
privately imports WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapLifts.
Its existing proof applies the upstream theorem unchanged. The upstream theorem drops
only the implicit Noetherian hypothesis, so every old use is a valid specialization.
Withdrawn the duplicate file through deleted.txt and repointed the node's Lean record
to the upstream theorem. No upstream files, consumer signatures or target statements change.
The adapted consumer compiled cleanly through lcompile.py (22.9 seconds).
The import-direction check permits the replacement. A textual comparison verifies
that the full upstream theorem and proof differ only by the removed hypothesis.
Change record: coord/changes/retire-finite-presentation-local-map-lifts.md.

## Proved and sorry left

The item had zero sorry holes before retirement. Its existing theorem
AlgebraicGeometry.exists_finitePresentation_local_map_lifts was already proved; the
upstream theorem has the same conclusion and a weaker hypothesis. Zero holes closed,
zero holes added, zero split off, zero remaining in the delivered Lean consumer.
AlgebraicGeometry.exists_finitePresentation_local_map_datum retains its complete proof.
This is a duplicate-module retirement, not a new proof or decomposition.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.FinitePresentationLocalMapLifts and removed its sole
private consumer import, replacing it with the upstream twin. The old module's imports
leave with the duplicate file; the upstream proof retains the one-chart lifting route.
No mathematical node or proof dependency is discarded: lem-pc-fp-local-map-lifts now
points to the surviving upstream theorem and still uses lem-pc-fp-one-chart-map-lift.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item, but the current queue marks this
module `retire`, and the item has no holes. Followed the human-approved retirement
instructions in coord/changes/retire-sheaf-twins-20261020.md. The upstream twin removes
the unused Noetherian hypothesis, which is the reported API difference. No new
statement or proof dependency is needed, and the unit's route is unchanged.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
