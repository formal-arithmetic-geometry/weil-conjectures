## What changed

Moved the shared definitions `twistChartOpen`, `twistChartFraction`, and `twistChartRead`
to `RelativeProjTwistChartDescentCompatibility`.  Added a node-backed
`RelativeProjTwistChartDescentCompatibility` predicate, then made the object component
return that compatibility and the transition component require it.  The target theorem is
proved by applying the two components.  The target module publicly imports the object
component and privately imports the transition component.

## Proved and sorry left

Closed the sorry in `AlgebraicGeometry.Scheme.GradedAlgebraData.exists_twist_chart_descent`.
The delivery adds the two strictly simpler split-off statements
`exists_twist_chart_descent_object` and `exists_twist_chart_descent_transition`; each retains
one documented `sorry` for its corresponding gluing argument.  The object statement now
returns `TwistChartCompatibility`, and the transition statement requires it.  The new
`TwistChartCompatibility` definition is sorry-free.

## No longer needed

The target proof no longer directly imports or names the raw tensor-pullback, relative-Proj,
or unit-to-twist modules; those are provided by the public object component through the
compatibility module.  The original three proof dependencies are replaced by the two
component nodes in the target's proof route.

## Where the brief, the DAG or earlier work was wrong

The prior delivery incorrectly allowed arbitrary chart choices in the transition theorem.
Such charts can be rescaled independently and need not satisfy the fraction equation.  The
repaired object component now returns normalized scalar-extension comparisons and their
commuting chart squares (`TwistChartCompatibility`), and the transition component requires
that datum.  The duplicate object import in the target was also removed.

## New nodes

`lem-trf-relative-proj-twist-chart-descent-object` records existence of the descended module
and chart isomorphisms in `RelativeProjTwistChartDescentObject`.

`lem-trf-relative-proj-twist-chart-descent-transition` records the compatible additive
transitions for a fixed descended module and chart family in
`RelativeProjTwistChartDescentTransition`.

`lem-trf-relative-proj-twist-chart-descent-compatibility` records the normalized scalar-
extension comparisons and commuting chart squares in
`RelativeProjTwistChartDescentCompatibility`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent": "bdf60b4f7180cf26066a1a0c005dda3906af1a6f", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentCompatibility": "50474c328ccab4b06612ef8050448925ed9635d3", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentObject": "aa768eb4ad26ca08841217c17847d557e56bb4da", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentTransition": "6104f245446d3dbaaec9abb08c262b2a1f6744f5"}, "results": {"Sheaf.AlgebraicGeometry.RelativeProjTwistChartFractionAdd": {"hash": "759a03aeceba77a19fa663a9153d27f92a92c831", "status": "OK"}, "Sheaf.AlgebraicGeometry.SymmetricProjAffineGeneratorLinear": {"hash": "74780bed89b0aa2341d82f52894ff338fdbb302e", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T05:48:06+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
