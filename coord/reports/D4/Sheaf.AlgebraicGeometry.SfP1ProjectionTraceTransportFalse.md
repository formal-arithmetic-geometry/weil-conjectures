## What changed

Removed the relabelled preconstant module and node from the returned delivery. Removed the unforced linter override from the restored `SfP1ChartExchange` source. Added `SfP1ProjectionTraceFalseMate` with a genuine false-projection chart-pasting factor, its inverse-cancellation statement, and a separate chart-tail statement. The target proof inserts and cancels the factor, applies chart pasting, and then applies the tail theorem.

## Proved and sorry left

`AlgebraicGeometry.Etale.SfP1Transport.projectionTraceTransport_false` is proved by a categorical `calc` from the three lower statements. `falseProjectionChartPasting` is proved from `chartExchange`. The two lower statements left as named sorries are `falseProjectionChartFactor_cancel` and `falseProjectionChartTail`; both are strictly smaller than the target and have complete proof plans in their docstrings. No definition contains a sorry.

## No longer needed

Removed the proof-only import and node for `SfP1ProjectionTraceTransportFalsePreconstant`; that relabelled target was not a valid decomposition. No existing DAG dependency is otherwise pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier repair introduced `projectionTraceTransport_false_preconstant`, which was equivalent to the target after composing with `constantComparison.inv`. The repair replaces it with a chart-exchange mate-pasting factor and a separate trace-tail statement, so the target is assembled from strictly smaller calculations. The `set_option linter.unusedSimpArgs false` line in `SfP1ChartExchange` was unforced and has been removed.

## New nodes

`lem-sf-p1-projection-trace-transport-false-chart-pasting` for the proved chart-pasting prefix, `lem-sf-p1-projection-trace-transport-false-factor-cancel` for inverse/direct-image cancellation, and `lem-sf-p1-projection-trace-transport-false-tail` for the post-chart trace tail, all in `lean/Sheaf/AlgebraicGeometry/SfP1ProjectionTraceFalseMate.lean`.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
