## What changed

Added `Sheaf.Paper.PodReindexingTensorSubstitutionCore`, which isolates the fixed-model construction and its three expression laws. The assigned theorem now packages that core with `PodCompletedTensorReindexing.Laws.Model` and `Canonical` without changing its statement.

## Proved and sorry left

The assigned theorem `WeilConjectures.podReindexingTensorSubstitution` is proved by direct existential packaging. One strictly smaller construction theorem remains as `sorry`: `WeilConjectures.podReindexingTensorSubstitutionCore` in node `lem-pod-reindexing-tensor-substitution-core`.

## No longer needed

No proof-dependency imports were removed. The proof uses the core construction and the tensor normalization laws supplied by `T`.

## Where the brief, the DAG or earlier work was wrong

The original item was too coarse for a direct proof: its target combines fixed-model construction with tensor normalization fields already present in `T.Laws`. The new node separates those responsibilities while preserving the target statement and unit route.

## New nodes

`lem-pod-reindexing-tensor-substitution-core` adds the strict fixed-model construction theorem in `Sheaf.Paper.PodReindexingTensorSubstitutionCore`; it is strictly weaker than the assigned target because it omits `T.Model` and `T.Canonical`, which are supplied directly by the caller.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorSubstitution": "97fc13c2dd93af8a59d5387903cbd70b02194ae0", "Sheaf.Paper.PodReindexingTensorSubstitutionCore": "b6eeaf6338d89909c3efb724bf228cca672adf02"}, "results": {}, "time": "2026-10-28T07:07:46+0800", "transitive": 0, "version": 1}
```

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
