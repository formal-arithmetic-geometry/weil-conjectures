## What changed

Added `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionIso`, proving the target quotient restriction transport by whiskering the existing `finiteComparison` isomorphism. Added `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso`, which states the remaining geometric target projection-model comparison. The assigned theorem now composes these two isomorphisms in `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso`.

## Proved and sorry left

`CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetQuotientIso` is proved. The assigned `CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetIso` is proved by composition. One strictly smaller intermediate theorem remains sorry: `CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetProjectionIso`, in `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso` (node `lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-projection-model-iso`). No definition contains a sorry.

## No longer needed

No imports or declared proof dependencies were pruned. The original target proof route is represented by the remaining projection-model node; the finite coefficient comparison is supplied by the existing `finiteComparison` declaration.

## Where the brief, the DAG or earlier work was wrong

The original DAG put the quotient identification and the geometric projection-model comparison in one proof step. The Lean API already proves the quotient part through `finiteComparison`; separating it exposes a real composition and leaves only the geometric comparison as an intermediate obligation. No target statement or existing declaration signature was changed.

## New nodes

`lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-quotient-iso` records the proved whiskered finite comparison. `lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-projection-model-iso` records the remaining geometric projection-model comparison and its source proof route.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso": "5e9f6ab7a7a8c0798c3c7f88b6e344a7e3b3e79d", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionIso": "5ba11ec35d592bc5ef2603722b0f8336ca2deb9c", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso": "88b445875fb281d1432b004d6dd49ec979a10943"}, "results": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation": {"hash": "b03c50985deafc6d83ff42627b8486802396a8c7", "status": "INFRA"}}, "seconds": 133, "time": "2026-10-28T08:07:05+0800", "transitive": 0, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
