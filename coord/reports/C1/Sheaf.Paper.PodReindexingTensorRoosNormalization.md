## What changed

Added `Sheaf.Paper.PodReindexingTensorRoosStrict`, which isolates the strict coherent-system Roos/model equivalence. The assigned theorem now obtains `Model` from that strict result; its separate `Canonical` hypothesis remains part of the public interface for compatibility with the parent construction.

## Proved and sorry left

The assigned theorem `podReindexingTensorRoosNormalization` is closed. One strictly lower equivalence theorem remains as `sorry`: `podReindexingTensorRoosNormalization_model_iff_canonical`, whose proof is the finite quotient, coherent transition, Roos-coordinate, and localization calculation described in its docstring.

## No longer needed

No imports or declared proof dependencies were pruned beyond the original route.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines the strict Roos realization and the Canonical cancellation in one theorem, but the available declarations only expose the separate Canonical equation. The strict coherent-system calculation therefore had to be recorded as a named lower theorem before the target could be assembled.

## New nodes

`lem-pod-reindexing-tensor-roos-strict` records `podReindexingTensorRoosNormalization_model_iff_canonical`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorRoosNormalization": "a2e7bbf1027ef91f0f8442f825e1fdd720fdc70a", "Sheaf.Paper.PodReindexingTensorRoosStrict": "26854c709ffd6eec18171bcca7bf2441b7442588"}, "results": {}, "time": "2026-10-28T08:19:36+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
