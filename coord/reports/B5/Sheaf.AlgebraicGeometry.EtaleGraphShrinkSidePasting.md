## What changed

Proved `AlgebraicGeometry.Etale.etaleGraphShrinkSidePasting`. The proof imports the existing open-shrinking comparison and middle pasting theorem, expands the graph comparison into its three factors, and applies a private categorical cancellation lemma. The module compiles with zero `sorry`s.

## Proved and sorry left

Closed 1 of 1 sorries: `AlgebraicGeometry.Etale.etaleGraphShrinkSidePasting`.

No sorries remain.

## No longer needed

The direct proof plan dependencies `lem-pur-etale-graph-neighborhood-geometry`, `lem-pur-etale-proper-open-exchange-cube`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-cbc-extension-zero-composition`, and `lem-amb-natural-transformation-whisker-exchange` are not needed directly. Their work is encapsulated by the imported open-shrink and middle-pasting declarations. The proof uses the existing `def-pur-etale-graph-neighborhood-words` statement dependencies and imports the two theorem modules listed above.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan expanded the proper/open exchange cube directly. The existing open-shrink comparison already packages that calculation, so the direct geometric and exchange dependencies were unnecessary for this item.

## New nodes

None.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
