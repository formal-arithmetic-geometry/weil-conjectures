## What changed

Added the proof-only import `Sheaf.Paper.DiagonalTraceFiniteProjection` and the new
proof module `Sheaf.Paper.DiagonalTraceFinitePushUnitSeed`. The target theorem now
rewrites the finite comparison, applies `diagonalTrace_finiteEvaluation_projection`,
uses the common-unit seed, and closes by categorical naturality, functoriality, and
isomorphism cancellation. The target node records this route. The seed is stated as
a strictly simpler equality before finite projection and evaluation.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finitePush_unit`.

Added one split-off hole, with node
`lem-sfb-diagonal-trace-finite-push-unit-seed`:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finitePush_unit_seed`.
It is the common-unit coefficient square before finite projection/evaluation and
has the completed exact-square, coefficient-cone, coefficient-pullback, limit,
and varying-comparison normalization as its source proof obligation.

## No longer needed

The target proof no longer directly uses the planned exact-cone projection route;
its finite projection step uses the existing specialized
`lem-sfb-diagonal-trace-finite-evaluation-projection`. No module is withdrawn and
no existing public declaration is removed. The new seed's own proof plan retains
its exact-cone projection dependency where needed.

## Where the brief, the DAG or earlier work was wrong

The original node compressed the common-unit normalization and finite evaluation
calculation into one step. The finite evaluation projection theorem provides the
second step directly, while the common-unit normalization is a separate strictly
simpler statement. No mathematical statement or definition is disputed.

## New nodes

`lem-sfb-diagonal-trace-finite-push-unit-seed` in
`dag/nodes/sec-six-functors-basics/lem-sfb-diagonal-trace-finite-push-unit-seed.json`
records the split-off seed and its source, proof plan, and declaration.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceFinitePushUnit": "ed3641474c9e6206ed4e382d6b355f1a04a22918", "Sheaf.Paper.DiagonalTraceFinitePushUnitSeed": "28dc568d04f4a4355977867b9dac381fbee395e6"}, "results": {}, "time": "2026-10-28T06:41:36+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
