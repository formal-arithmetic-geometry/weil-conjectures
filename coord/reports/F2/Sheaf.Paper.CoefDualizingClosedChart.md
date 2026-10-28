## What changed

Closed the two-level coefficient assembly theorem by reducing it to two applications
of a new one-level coefficient theorem. The affine-space chart existence theorem and
all existing declarations are unchanged. The target theorem therefore remains a real
proof assembled from the source-library affine chart construction and the named
coefficient package.

## Proved and sorry left

Closed one existing hole:

- `AlgebraicGeometry.Etale.coefClosedChartAt_of_closed_chart`.

Added one strictly smaller named hole:

- `AlgebraicGeometry.Etale.coefClosedChartAt_single_of_closed_chart`, recorded by
  node `lem-coef-dualizing-closed-chart-single`.

The remaining hole is one coefficient level with a fixed closed chart; it has no
finite-field presentation, no affine-chart existential, and no second coefficient
stage. No definition contains `sorry`.

## No longer needed

No imports or modules are removed. The two-level helper's proof no longer depends
on the full eight-step plan directly; it uses only the one-level coefficient node.
The target's geometric proof uses `exists_isClosedImmersion_affineSpace_of_isAffine`
and the coefficient helper, while the broad imports remain necessary for the public
helper definitions in this module.

## Where the brief, the DAG or earlier work was wrong

The prior delivery had already isolated the geometric chart argument but left the
two coefficient stages bundled in one admitted theorem. The two stages are
independent once the chart is fixed, so the remaining work can be stated as a
strictly smaller one-stage theorem and assembled by a complete Lean proof. The
historical global-build record reports a bad import for
`Sheaf.Paper.EtaleCompactSupportCoefficientChange`, but the current source and
single-file compiler resolve that import; no import workaround was introduced.

## New nodes

- `lem-coef-dualizing-closed-chart-single` records the one-positive-coefficient
  component of the fixed-chart argument, with its source and complete proof plan.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefDualizingClosedChart": "7cb3d50bcca8580d6a454bb566e73e01c6555ad8"}, "results": {}, "time": "2026-10-28T07:51:24+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
