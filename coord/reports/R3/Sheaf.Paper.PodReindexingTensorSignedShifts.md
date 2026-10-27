## What changed

Replaced the proof of `WeilConjectures.podReindexingTensorSignedShifts` by a real assembly proof. The large signed-shift argument is split into two strictly lower public theorems: `Sheaf.Paper.PodReindexingTensorSignedShiftsCore` supplies the two shift models and the reduction, limit, Roos, generator, and representative-model laws; `Sheaf.Paper.PodReindexingTensorSignedSquares` supplies the two tensor-factor reindexing squares. The target combines these components into the unchanged `PodReindexSignedShifts` definition.

## Proved and sorry left

Closed the original `podReindexingTensorSignedShifts` hole. Added two whole named public theorem holes, each with its own node and proof description: `podReindexingTensorSignedShifts_core` (node `lem-pod-reindexing-tensor-signed-shifts-core-r3`) and `podReindexingTensorSignedShifts_tensorSquares` (node `lem-pod-reindexing-tensor-signed-shift-squares-r3`). This is a decomposition of the one original obligation; no sorry remains in the assigned module.

## No longer needed

No existing proof imports or declared dependencies were removed. The assigned module now imports only the two split proof modules in addition to its existing public definition import.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan described two independent constructions but provided no Lean declarations for either intermediate result. The decomposition makes those strictly smaller steps explicit while preserving the unit route and the exact target statement.

## New nodes

`lem-pod-reindexing-tensor-signed-shifts-core-r3` records the core shift-model and model-law construction. `lem-pod-reindexing-tensor-signed-shift-squares-r3` records the two final tensor-factor equations. Both inherit the item's chapter and unit and retain the stated signed Roos and K-flat tensor dependencies.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorSignedShifts": "549dc58aac356ed0a32e2300b63bea0b9aa50adf", "Sheaf.Paper.PodReindexingTensorSignedShiftsCore": "aae25179f9f64501e8d556a30d240922d9bae4f2", "Sheaf.Paper.PodReindexingTensorSignedSquares": "c536f2076824c7ce506f9f0ede7b551b98a72f41"}, "results": {}, "time": "2026-10-28T07:07:00+0800", "transitive": 0, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
