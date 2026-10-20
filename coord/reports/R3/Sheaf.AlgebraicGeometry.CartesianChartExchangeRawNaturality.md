## What changed

Withdrew the duplicate Sheaf module
`lean/Sheaf/AlgebraicGeometry/CartesianChartExchangeRawNaturality.lean`.
The corresponding source module
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeRawNaturality` is retained
and supplies the same raw comparison naturality declarations to its importer.
The retirement is recorded in `coord/retire-items.tsv`; the required change record is
`coord/changes/retire-cartesian-chart-exchange-raw-naturality.md`.

## Proved and sorry left

No theorem holes were closed or added. The withdrawn Sheaf module had no `sorry`:
its two private naturality helpers were already proved. The retained upstream twin
contains the declarations used by the live source importer.

## No longer needed

The duplicate Sheaf module and its proof-only import of
`WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality`
are no longer needed. No live module imports the Sheaf twin; the source
`CartesianChartExchangeMapNaturality` imports the retained WeilConjectures twin.
The retirement row identifies the source twin as the kept implementation and
lists the duplicate's former dependency closure.

## Where the brief, the DAG or earlier work was wrong

The assigned item was a duplicate twin retirement rather than an open theorem:
the Sheaf module was already sorry-free, while the source twin is the live module.
The queue claim therefore required withdrawal under the recorded retirement row,
not a new proof or a changed statement.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
