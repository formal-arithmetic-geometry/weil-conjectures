## What changed

Completed the listed retirement of
Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction. Its three private
definitions and eight private proved lemmas/theorems have token-identical
upstream implementations, ignoring comments and whitespace. Switched the private
proof import in CartesianChartExchangeComparison and CartesianChartExchangeTransport
to WeilConjectures.AlgebraicGeometry.CartesianChartExchangeAdjunction and listed
the duplicate in deleted.txt. Comparison also disables the privateModule linter
for this intentionally private helper module; the initial compile reported that existing warning.

Change record: coord/changes/C2-cartesian-chart-exchange-adjunction-retirement.md.
CartesianChartExchangeEvaluation additionally receives a proof-only speed repair:
keep concrete derived constructions locally folded and use two proved generic
private helpers, shifted_add_equiv_eval and cancel_iso_eval. The original file
hit the 60-second limit; the repaired file compiles cleanly in 12.4 seconds.
The existing cartesianChartAdjunct_spec and chartCohomologyIso_eval signatures
are unchanged. The three changed downstream consumers compile in import order.
The import-closure audit adds no twin pairs.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero split off.
No remaining sorry declarations in the retired module or the changed consumers.
The existing complete upstream proofs supply every former use. This delivery is
a duplicate retirement, not new proof progress.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction and both direct
imports of it. The upstream twin preserves all required mathematics. No DAG
node or unit references the retired module; no quarantined parent references it.
No nodes are withdrawn, and no other module or dependency is claimed unnecessary.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes, but the current queue and
retirement table classify this item as a zero-hole duplicate retirement. The
historical SUPERSET/kept classification predates prerequisite retirements: the
current modules have identical imports and declaration tokens, and the current
consumer audit introduces no duplicate module pairs. The downstream validation
exposed a slow Evaluation proof: diagnostics found
normalization of the concrete derived adjunction and chart isomorphisms; an
import-only probe took 6.6 seconds. The proof repair uses explicit equations and
generic evaluation identities and leaves no diagnostic options or budget changes.
No mathematical statement, source-library declaration or target changes.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
