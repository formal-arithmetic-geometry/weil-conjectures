## What changed

Filled `WeilConjectures.PurityFiniteSetting.ChartDiagonalSourceMate.productGeometry`
in `Sheaf.Paper.ChartDiagonalSourceMate`, preserving its statement and all constructions.
Factor the self-product map through `ChartFactors.sourceLift` followed by the pullback
of the chart map. The existing `ChartFactors.sourceLift_geometry` supplies the first
factor's properties, and stability under base change and composition supplies those
of the composite. Separatedness of the chart follows by cancellation from `h`;
Noetherianity of its finite-type field domain supplies quasi-compactness. The two
projection identities and the diagonal identity follow from the pullback equations.

This is a partial delivery for a module with two holes. The main mate calculation
remains unchanged. Its existing six-step proof plan and stated dependencies are retained.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.PurityFiniteSetting.ChartDiagonalSourceMate.productGeometry`.

One original hole remains:
`WeilConjectures.PurityFiniteSetting.ChartDiagonalSourceMate.chartDiagonalSourceMate`
(blueprint `lem-pur-chart-diagonal-source-mate`). No holes added or split off.

The geometry proof covers empty U and d = 0 without exclusions. It uses only
pullback identities, the existing source-lift geometry, and standard morphism
permanence; it makes no coordinate-orientation choice.

## No longer needed

None. No imports, nodes or modules are withdrawn. The unchanged main theorem still
needs its existing mate-pasting, normalization and site-transport proof plan.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The shorter proof of the geometry helper reuses the
already proved source-lift geometry, rather than reconstructing its Cartesian square.
Searches with leanfinder, loogle and grep found the existing pullback permanence API;
source inspection found `ChartFactors.sourceLift_geometry` in
`Sheaf.Paper.ChartDncVectorFactorData`. The separate
`ChartComparisons.chart_diagonal_source_square` applies to affine chart objects and
does not directly supply the main theorem for an arbitrary, possibly non-affine U.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
