## What changed

Retire the listed duplicate Sheaf.AlgebraicGeometry.CartesianChartExchangeCore.
Its three private lemma signatures and full proofs match the upstream twin.
Migrate the private Core import in CartesianChartExchangeSource,
CartesianChartExchangeAdjunction and CartesianChartExchangeTransport to
WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCore. Each consumer
changes exactly one import line; all declarations, proofs and public imports
stay identical. The upstream source is untouched.

Change record: coord/changes/C3-cartesian-chart-exchange-core-retirement.md.

Validation: all three changed consumers compile without warnings. All eight
transitive consumers also compile against the delivered import edits.
The unchanged CartesianChartLiftRawNaturality and CartesianChartLiftNaturality
retain their existing long-line and letI style warnings; they are validation
copies only and are excluded from the delivery.
A source import-closure comparison finds no new twin pairs in any consumer;
the three Lift consumers lose the Core pair. No DAG, unit, chapter, note or
quarantined source references the retired module. Library sources have no
remaining import of it after applying the three edits.

## Proved and sorry left

Actual initial holes: 0. Closed: 0 of 0. Added: 0. Split off: 0. Left: none.
The already-proved private lemmas single_source, single_restriction and square_comp
are preserved in the upstream twin; this is duplicate retirement, not a new proof
or decomposition. All adapted consumers retain zero holes.

## No longer needed

Sheaf.AlgebraicGeometry.CartesianChartExchangeCore is withdrawn. Its private
imports at all three direct consumers are replaced by the upstream twin.
No mathematical dependency or DAG node is pruned: no node was attached to this
helper module. No additional module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with a hole, but the current item is
an authorized retirement listed in coord/retire-items.tsv, with zero holes.
The old SUPERSET warning is stale for the current dependency environment:
the three declarations and proofs now agree exactly, all migrated direct
consumer closures are free of twin pairs, and no new pair arises downstream.
No target statement or unit route changes.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
