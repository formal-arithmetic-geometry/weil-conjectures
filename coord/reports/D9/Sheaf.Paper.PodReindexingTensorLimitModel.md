## What changed

The item theorem now applies the strict-model localization descent statement to the
`Model` and `Naturality` conjuncts of `PodCompletedTensorReindex.Laws`.  I added the
proof-only module `Sheaf.Paper.PodReindexingTensorLimitModelDescent` and updated the
item node's proof route to record that intermediate step.  Both sandbox modules
compile in import order.

## Proved and sorry left

`WeilConjectures.podReindexing_tensor_limit_model` is proved (one hole closed).
The new `WeilConjectures.podReindexing_tensor_limit_model_descent` theorem remains
as one named `sorry`: it is the strict good-complex transport and fully faithful
localization descent step described in its docstring (one hole split off).

## No longer needed

No imports or declared dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan expands a full strict-tensor and localization descent
argument that is not available as a single declaration.  The item can nevertheless
be reduced cleanly to that argument as a named intermediate theorem; the parent
combination from the recorded `Model` and `Naturality` laws is complete.

## New nodes

`stage3-pod-reindexing-tensor-limit-model-descent` records the strict-model transport
and descent theorem used by the item.  Its source is the same blueprint proof,
Steps 2 and 4, with Stacks 07A4, 08TC and 0941.  The theorem is strictly the
representative-to-localization descent substep and is stated in
`Sheaf.Paper.PodReindexingTensorLimitModelDescent`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorLimitModel": "e7845dc499daadf8d368cecc8191cd72a3379cb2", "Sheaf.Paper.PodReindexingTensorLimitModelDescent": "13195861040c7e66e26ae4446eddf389e3ae92cd"}, "results": {}, "time": "2026-10-28T05:22:09+0800", "transitive": 0, "version": 1}
```

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
