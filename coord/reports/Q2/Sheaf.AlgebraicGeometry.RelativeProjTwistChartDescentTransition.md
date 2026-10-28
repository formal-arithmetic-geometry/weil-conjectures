## What changed

Proved the transition theorem from the compatibility witness by defining the additive map as the
section-normalized pullback unit followed by the scalar-extension comparison, transported across
the equality of chart preimages. The two compatibility conjuncts were split into the named
intermediate modules `RelativeProjTwistChartDescentTransitionRead` and
`RelativeProjTwistChartDescentTransitionFraction`; each has a documented `sorry` for its
strictly simpler conjunct. Updated the item DAG node to record these proof dependencies.

## Proved and sorry left

The item theorem `exists_twist_chart_descent_transition` is proved. Two intermediate theorem
holes remain: `twist_chart_transition_read` in node
`lem-trf-relative-proj-twist-chart-descent-transition-read`, and
`twist_chart_transition_fraction` in node
`lem-trf-relative-proj-twist-chart-descent-transition-fraction`.

## No longer needed

No declared proof dependency was pruned. The transition proof uses the scalar-extension
comparison and section-normalized tensor pullback declarations recorded in the item node.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan hid two independent coherence calculations. They are now explicit
strictly simpler statements, one for read compatibility and one for the denominator-one fraction
formula.

## New nodes

`lem-trf-relative-proj-twist-chart-descent-transition-read` records the read-compatibility
conjunct and is stated in `lean/Sheaf/AlgebraicGeometry/RelativeProjTwistChartDescentTransitionRead.lean`.

`lem-trf-relative-proj-twist-chart-descent-transition-fraction` records the homogeneous-fraction
conjunct and is stated in `lean/Sheaf/AlgebraicGeometry/RelativeProjTwistChartDescentTransitionFraction.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentTransition": "a92c9d3d48e58faa0f8362ca38f6f897a422569e", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentTransitionFraction": "d6453297c6d0365d476ed07e0266fbaaee6d4386", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentTransitionRead": "342eaba7032807bd857992fe221ae4371bbd2b2a"}, "results": {}, "time": "2026-10-28T08:20:34+0800", "transitive": 0, "version": 1}
```

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
