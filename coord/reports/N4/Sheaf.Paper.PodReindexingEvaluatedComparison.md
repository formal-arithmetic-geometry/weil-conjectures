## What changed

Added two intermediate modules, `Sheaf.Paper.PodReindexingComparisonCore` and
`Sheaf.Paper.PodReindexingEvaluationLaw`, and imported them privately in the item.
The item theorem now combines the core normalized `Comparison` witness with the
separate evaluation law.

## Proved and sorry left

The item theorem `evaluated_comparison_exists` is proved from the two strictly
smaller intermediate statements. The new declarations `comparison_core_exists`
and `comparison_evaluation_law` remain `sorry`, each with its own DAG node.

## No longer needed

The item proof no longer directly imports or cites the six lower proof dependencies
listed in the original plan; they are encapsulated by the two intermediate nodes.
No existing library module was removed.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the construction of all `Comparison` fields and the
independent evaluation argument into one theorem. The implementation split these
strictly separate obligations into a core data existence statement and an evaluation
law with a supplied comparison, allowing the target theorem to compile while
preserving its exact statement.

## New nodes

`lem-pod-reindexing-comparison-core` records the normalized comparison-data
construction. `lem-pod-reindexing-evaluation-law` records the evaluation identity
for a supplied comparison. Both are in `dag/nodes/sec-poincare-duality/`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingComparisonCore": "7ae7848320a3cd3e1bb27a899d9be171095af1d0", "Sheaf.Paper.PodReindexingEvaluatedComparison": "2e33a5c8733d7ec6c095da58f11d4f1853128470", "Sheaf.Paper.PodReindexingEvaluationLaw": "2903ea1dd041452d2994626b30a0073228496bc6"}, "results": {}, "time": "2026-10-28T07:05:15+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
