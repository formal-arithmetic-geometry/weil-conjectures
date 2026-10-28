## What changed

Proved `WeilConjectures.PodReindexingCoherence.source_right_normalization` in
`Sheaf.Paper.PodReindexingSourceRightNormalization`, following the existing three-step DAG plan.
The proof specializes the normalized signed source shift, identifies the ordinary Hom comparison
with the inverse recorded Hom model, cancels the model factors in `Comparison.derived_model`, and
uses a proved private categorical helper for localization-factor naturality and shift compatibility.
The theorem signature, public import, definitions, instances and attributes are unchanged. The item
node records the actual proof. No other existing module was changed.

Validation: the complete item compiled cleanly through `lcompile.py` in 16.3 seconds, with no
compiler errors or warnings. The delivered theorem signature was compared with the original
and is unchanged; the module contains no `sorry` token and all Lean lines fit 100 characters.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PodReindexingCoherence.source_right_normalization`
(node `lem-pod-reindexing-source-right-normalization`).

Holes closed: 1. Holes added: 0. Sorries left in the item: 0. Split off: 0.
The private helper `right_model_calculus` is proved without holes. This is a proof from the existing
declarations, with no new assumed intermediate theorem.

## No longer needed

None. The proof uses the existing model factors, ordinary Hom comparison, normalized source shift,
coherence data, and localization functors, so all recorded proof dependencies remain needed.
No import, node or module is pruned, and no new import was added.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found in the statement or the planned route. Projectionwise uniqueness
of `LeftFormula` is private in the source module, so the proof repeats its short extensionality
argument locally rather than changing that module's interface. The unit route is unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingSourceRightNormalization": "717cee050432ab19b5ce31cc658b120ebd56c966"}, "results": {"Sheaf.Paper.PodReindexingDerivedSourceShiftModel": {"hash": "56106e7b2b8a800d2e55fcd9e35026b6c315017f", "status": "OK"}}, "seconds": 89, "time": "2026-10-28T14:12:28+0800", "transitive": 0, "version": 1}
```

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
