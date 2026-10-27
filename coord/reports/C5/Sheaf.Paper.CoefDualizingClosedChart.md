## What changed

Added the source-library affine closed-chart theorem import and proved the geometric part of `exists_coefDualizingClosedChart` using `exists_isClosedImmersion_affineSpace_of_isAffine`. The chosen closed immersion now supplies finite, proper, locally finite type, and quasi-compact instances, and the target delegates the two coefficient clauses to the split theorem `coefClosedChartAt_of_closed_chart`.

## Proved and sorry left

Closed the geometric existence and morphism-property portion of `exists_coefDualizingClosedChart`. One sorry remains in `coefClosedChartAt_of_closed_chart`; it is the coefficient-theoretic bounded-below compact-support and counit-normalization argument for the two levels.

## No longer needed

None. The existing imports remain required by the helper definitions and the split coefficient theorem. The new `WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart` import is required for the proved geometric step.

## Where the brief, the DAG or earlier work was wrong

The global build record reported a bad import for `Sheaf.Paper.EtaleCompactSupportCoefficientChange`, but the current source and sandbox compiler resolve that module successfully. No statement was changed.

## New nodes

Added `lem-coef-dualizing-closed-chart-properties` for `coefClosedChartAt_of_closed_chart`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefDualizingClosedChart": "75e959bec87c22a34a2fdbaf5e2282ed3f4d76e2"}, "results": {}, "time": "2026-10-28T06:44:01+0800", "transitive": 0, "version": 1}
```

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
