## What changed

Added `Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponentCore`, which records the
explicit expansion of the mapped cochain component used by the assigned theorem. The assigned
component theorem now unfolds `ordinaryPullEvaluationComplex` and applies this core statement.
Both modules compile in import order.

## Proved and sorry left

The assigned declaration `integralPullEvaluation_cochainSquare_component` is proved from the
new explicit component theorem. The new declaration
`integralPullEvaluation_cochainSquare_component_core_expanded` remains `sorry`; it is the
sectionwise degree calculation from Construction 4.1 and is recorded by the new DAG node
`lem-sf-integral-pull-evaluation-cochain-square-component-core`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted that the mapped homological-complex component must first be
expanded to expose the degreewise module-map identity. The new core node records that missing
intermediate statement.

## New nodes

`lem-sf-integral-pull-evaluation-cochain-square-component-core` in
`dag/nodes/sec-six-functors/lem-sf-integral-pull-evaluation-cochain-square-component-core.json`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponent": "942cd266f24310d3549a2a163c59baca32683b68", "Sheaf.SixFunctors.IntegralPullEvaluationCochainSquareComponentCore": "7a09d66daba373bb4a6e0b87d4822b2005e2e956"}, "results": {"Sheaf.SixFunctors.IntegralPullEvaluationCochainSquare": {"hash": "982ef542132ea8512c315dce1d8789a7d3422a9e", "status": "OK"}}, "seconds": 39, "time": "2026-10-28T08:33:13+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
