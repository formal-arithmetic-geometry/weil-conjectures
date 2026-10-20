## What changed

Retired `lean/Sheaf/AlgebraicGeometry/CartesianChartExchangeEvaluation.lean`
and listed it in `deleted.txt`. The remaining consumer,
`lean/Sheaf/AlgebraicGeometry/CartesianChartExchangeComparison.lean`, changes
one proof import from the duplicate to
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeEvaluation`. Its
private uses of `cartesianChartAdjunct_spec` compile against the upstream twin.
The node `lem-sc-cartesian-chart-cohomology-evaluation` now points to the
upstream declaration. The change record is
`coord/changes/E5-cartesian-chart-exchange-evaluation-retirement.md`.

## Proved and sorry left

The item had zero `sorry`s before this retirement and zero `sorry`s are left.
No declaration is added and no hole is split off. The upstream twin supplies the
complete proofs.

## No longer needed

The duplicate Sheaf module and its private helper declarations are no longer
needed. The Sheaf Evaluation proof import is removed from
`CartesianChartExchangeComparison`; the upstream Evaluation import replaces it.
`CartesianChartRestrictedMapEvaluation` was already a withdrawn empty module,
so it needs no change. No additional DAG nodes or unit dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned item was a zero-hole duplicate retirement rather than an open proof
hole. The retirement table's listed RestrictedMapEvaluation consumer had already
been withdrawn, leaving only ExchangeComparison to adapt. The upstream twin
provides the required private declarations with compatible signatures.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
