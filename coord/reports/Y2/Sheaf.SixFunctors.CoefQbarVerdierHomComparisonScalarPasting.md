## What changed

The assigned module now proves `component_extension_of_scalar_compatibility` by
reducing it, after the explicit `component` presentation, to the narrower
`component_extension_expanded` finite-stage local-comparison square. The generic
`scalar_evaluation_transport` helper remains proved and is available to the
finite-stage argument. The proof-only `RationalHomScalarEvaluation` import was
removed because the scalar compatibility type is already exposed by the component
imports.

## Proved and sorry left

The outer declaration `component_extension_of_scalar_compatibility` is proved.
The remaining sorry is `component_extension_expanded`, whose node is
`lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded`; it is the finite
Hom evaluation, beta, omega, and transition cancellation calculation.

## No longer needed

The proof-only import `Sheaf.SixFunctors.RationalHomScalarEvaluation` is no longer
needed. No other declared dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the full component equality as one calculation.
Expanding `component` exposes a distinct finite-stage local-comparison square, so
that square is recorded as the remaining strictly smaller proof step. No target
statement or existing definition was changed.

## New nodes

`lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded` records the
expanded finite-stage local-comparison square and its proof plan. Its Lean
statement is in the assigned module as `component_extension_expanded`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting": "22d076d3a202dc1349a010819d6d9aa7cc283163"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension": {"hash": "07fc8904e746be96946dc114a18ebeada077a569", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T09:52:06+0800", "transitive": 0, "version": 1}
```

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
