## What changed

Proved `WeilConjectures.AdicQbarRealization.completed_tensor_finite_model` by obtaining the existing normalized completion presentation and assembling it with the new `CompletedTensorFiniteModelCore`. Added `Sheaf.Paper.AdicCompletedTensorFiniteModelCore`, which packages the scalar-extension balance, K-flat transport, ordinary comparison, and representative equation needed after the completion presentation is fixed.

## Proved and sorry left

Closed the item theorem `WeilConjectures.AdicQbarRealization.completed_tensor_finite_model` (1 of 1 original sorries). Added one strictly smaller split theorem, `WeilConjectures.AdicQbarRealization.completed_tensor_finite_model_core`, with one sorry; its node is `new-sf-adic-completed-tensor-finite-model-core`.

## No longer needed

No imports or declared dependencies were removed. The proof uses the completion presentation and the new core only; the prior plan's direct imports of the cochain pullback coherence and generic derived tensor pullback are confined to the core node's proof dependencies and are not imported by the item module itself.

## Where the brief, the DAG or earlier work was wrong

The prior proof plan treated the completion presentation, scalar-extension comparison, K-flat transport, and representative descent as if they were already packaged by the item imports. They are separate data: the completion presentation is available from `constructibleTensorCompletionPresentation`, while the remaining clauses require a named intermediate core statement.

## New nodes

`new-sf-adic-completed-tensor-finite-model-core` records the strictly smaller scalar-extension and K-flat core used to assemble the item.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorFiniteModelCore": "17fafd7a77c6623a115ebe1fcd33da66e3ec23b9", "Sheaf.Paper.AdicCompletedTensorFiniteModelExistence": "893b8cf937f3df5d0dd9cfb168b68b7d868b8b21"}, "results": {}, "time": "2026-10-28T04:09:57+0800", "transitive": 0, "version": 1}
```

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
