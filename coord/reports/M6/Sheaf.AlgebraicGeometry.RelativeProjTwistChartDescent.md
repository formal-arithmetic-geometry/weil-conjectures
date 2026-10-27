## What changed

Added the named local fraction substep `twistChartFraction_add` in
`Sheaf.AlgebraicGeometry.RelativeProjTwistChartFractionAdd`. The substep is delivered in a separate proof module importing the target interface. The target signature and all existing
definitions are unchanged; the target descent proof remains open.

## Proved and sorry left

The target declaration `AlgebraicGeometry.Scheme.GradedAlgebraData.exists_twist_chart_descent`
still has its original `sorry`.

The new declaration `AlgebraicGeometry.Scheme.GradedAlgebraData.twistChartFraction_add`
is a named split-off theorem with a `sorry`; its node records the pointwise localization
proof required to close it. No definition contains a `sorry`.

## No longer needed

None. The local fraction additivity node is a strict substep of the target's third proof
step; no existing target dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's third step treats additivity of the normalized fraction transition as an
implicit calculation. It is a separate local lemma and is now stated explicitly so it
can be proved independently before the sheaf descent argument.

## New nodes

`lem-trf-relative-proj-twist-chart-fraction-add` records the new local fraction
additivity theorem and its Lean declaration.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent": "baf2f9c842c84896b14b232f90c92c465ff26802", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartFractionAdd": "759a03aeceba77a19fa663a9153d27f92a92c831"}, "results": {}, "time": "2026-10-28T03:42:30+0800", "transitive": 0, "version": 1}
```

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
