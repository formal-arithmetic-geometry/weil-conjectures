## What changed

Repaired `Sheaf.AlgebraicGeometry.SfP1ChartMapComposition.chartMap_compHom` against the current F1 coefficient interface. The returned global build stopped at `hrefl` because the chart map now uses the irreducible `ordinaryFiniteChartTransport` wrapper. The proof conversion explicitly unfolds this wrapper and `ordinaryFiniteAdjunction`, while retaining the natural-transformation comparison argument and explicit congruence for recorded instances. The public statement and public imports are unchanged. Only the item module and its own proof node are changed.

## Proved and sorry left

Closed the single original hole in `AlgebraicGeometry.Etale.SfP1Transport.chartMap_compHom` (node `lem-sf-p1-chart-map-composition`). No holes added; no split statements; zero `sorry` left in the item module. All private helpers are proved. The repaired item compiled in 12.3 seconds in the single-file check. A second check compiled the item together with its unchanged direct consumer `SfP1ChartExchange`. The axiom check for `chartMap_compHom` reports only `propext`, `Classical.choice`, and `Quot.sound`. The temporary consumer probe was removed from the packet.

## No longer needed

None of the declared proof dependencies is pruned: the chart equation and chart-map construction remain used. No imports removed. No new dependency on exchange, trace, or twist-composition identities is needed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous delivery's normalization handled the earlier direct composite in the chart-map definition. The current source instead packages that composite in `ordinaryFiniteChartTransport`, with its unit packaged in `ordinaryFiniteAdjunction`; both are irreducible. The global build exposed this interface drift. The repair expands exactly these additional wrappers and leaves their definitions unchanged. The dispatched sandbox contained only launcher metadata at the start of this repair, so the proof was reconstructed from the retained session record and the current source, preserving its mathematical argument.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
