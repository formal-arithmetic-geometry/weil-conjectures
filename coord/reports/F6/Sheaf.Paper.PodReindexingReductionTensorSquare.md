## What changed

Added `Sheaf.Paper.PodReindexingReductionTensorSquareDescent`, whose public theorem
isolates the strict pure-tensor representative calculation and its descent through the
product K-flat localization. The item theorem now unfolds its frame and applies this
named descent theorem to the recorded comparison's `tensorChain_pure` field.

## Proved and sorry left

Closed `podReindexing_reduction_tensor_square` in the item module.

Added `podReindexing_reduction_tensor_square_descent`; its proof remains `sorry`.
It is the strict representative calculation plus localization descent, with source and
proof plan recorded in its node and docstring.

## No longer needed

None. All existing imports remain used by the item or by the split-off descent module.

## Where the brief, the DAG or earlier work was wrong

The earlier private mate-calculus lemma was insufficient: it did not connect the
sectionwise pure-tensor normalization to the derived system comparison. The unresolved
part is now stated as a public intermediate descent theorem rather than left inside the
target proof.

## New nodes

- `lem-pod-reindexing-reduction-tensor-square-descent`: strict pure-tensor comparison
  and K-flat localization descent.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingReductionTensorSquare": "126e1e6a14eb255b600fb215344650bd27f17af2", "Sheaf.Paper.PodReindexingReductionTensorSquareDescent": "0f6078e473ad30838a39793bd0623310b78ea859"}, "results": {}, "time": "2026-10-28T05:56:51+0800", "transitive": 0, "version": 1}
```

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
