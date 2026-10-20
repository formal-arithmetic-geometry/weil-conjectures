## What changed

Retired the listed duplicate Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport
in favor of WeilConjectures.AlgebraicGeometry.CartesianChartExchangeTransport.
The two direct consumers, CartesianChartExchangeEvaluation and
CartesianChartExchangeComparison under Sheaf.AlgebraicGeometry, change only
one private import each, retaining `import all` to access the private helpers.

All eight private lemma signatures and complete proofs in the retired module
match the upstream implementation modulo comments and whitespace. No upstream
file, consumer declaration, public import, mathematical definition or target
statement changes. The canonical transport construction and its naturality
proof are retained upstream, rather than bypassed.

Change record: coord/changes/G9-cartesian-chart-exchange-transport-retirement.md.

Validation: both migrated consumers compile without errors or warnings on the
server (Evaluation 11.5 seconds; Comparison 26.4 seconds). The unchanged
CartesianChartLiftCoherence also compiles against the overlay (39.1 seconds).
Extra checks of CartesianChartLiftRawNaturality and CartesianChartLiftNaturality
hit the unchanged 60-second limit, both against the migrated overlay and in
separate baseline compiles without the overlay. RawNaturality also timed out
on a second overlay attempt. These are pre-existing transitive compilation
limitations; no compiler error attributable to this retirement was observed.
The unchanged validation copies are not delivered. The maintainer's global
build remains the final check of these two transitive consumers.
A source import-closure audit of all five finds no new twin-module pairs and
no remaining reachability of the retired module. Both direct consumers have
no twin pairs. Each Lift consumer loses the Transport pair and retains only
the pre-existing Comparison and Evaluation pairs.

## Proved and sorry left

This retirement item starts with zero sorries and ends with zero sorries.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
All eight already-proved private lemmas are retained in the upstream twin:
add_iso_trans_apply, yoneda_mapIso_apply, coyoneda_mapIso_apply,
chartAdjunct_as_actual, chartCoefficient_hom, chart_inv_diagonal,
chart_inv_leg and chartAdjunct_pullback. Both adapted consumers are sorry-free.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/CartesianChartExchangeTransport.lean
through deleted.txt. Remove its private proof import from
Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation and
Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison, replacing each with
the upstream twin. Every current direct reference is migrated in this packet.
No mathematical proof dependency is pruned; no DAG node or unit points at
this implementation copy, and no quarantined Lean source references it.
No new nodes or node changes are required.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed theorem, but the actual assignment
is the explicit zero-hole retirement row in coord/retire-items.tsv. The older
kept-copy table lists this module as SUPERSET because its twin previously
brought in other kept copies. Those lower dependencies have since migrated:
the current Transport import headers agree, and the eight lemma bodies agree.
The current closure audit confirms the retirement creates no new twin pairs.
No mathematical statement or unit route was found wrong.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
