## What changed

The core theorem now obtains a raw comparison-data witness, applies five independently
stated law theorems to that same witness, assembles `PodReindexingDerivedData`, and
proves `CoreLaws` by conjunction.  Added `PodReindexingDerivedCoreData` and its
assembly helper, plus one split theorem module for raw-data existence and one for
each of `ReductionEvaluation`, `LimitProjection`, `Unit`, `FiniteModel`, and
`LimitModel`.  The item module imports those proof-only modules; its public target
statement is unchanged.

## Proved and sorry left

Closed the existing `podReindexingDerivedComparisonsCore` sorry (1 of 1 in the item).
The delivery adds six strictly smaller split obligations, each intentionally left as
one named `sorry`: `podReindexingDerivedCoreData_exists`,
`podReindexingDerivedCoreData_reductionEvaluation`,
`podReindexingDerivedCoreData_limitProjection`,
`podReindexingDerivedCoreData_unit`,
`podReindexingDerivedCoreData_finiteModel`, and
`podReindexingDerivedCoreData_limitModel`.  Their DAG nodes are listed under
`## New nodes`.

## No longer needed

None.  The strict comparison, coefficient evaluation calculus, exact product/Roos
limit comparison, and primitive quotient realization dependencies remain needed by
the split construction and are represented in the updated proof dependency route.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan had no Lean declarations that package the five
assembled laws together.  It was therefore decomposed into raw map existence and
five individual law statements, each strictly simpler than the target.  No target
statement or existing declaration signature was changed.

## New nodes

Added `def-pod-reindexing-derived-core-data` for the raw map record,
`lem-pod-reindexing-derived-core-data-existence` for its existence, and the five law
nodes `lem-pod-reindexing-derived-core-reduction-evaluation`,
`lem-pod-reindexing-derived-core-limit-projection`,
`lem-pod-reindexing-derived-core-unit`,
`lem-pod-reindexing-derived-core-finite-model`, and
`lem-pod-reindexing-derived-core-limit-model`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingDerivedComparisonsCore": "17a9f282d9d87372fb63f9628de9885184021152", "Sheaf.Paper.PodReindexingDerivedCoreData": "41fd72fd1b0e3986c47c84ea0f95c3518119e1d1", "Sheaf.Paper.PodReindexingDerivedCoreDataExistence": "bc60cbd04cab6ef64a7cfa613914d333888b7c7c", "Sheaf.Paper.PodReindexingDerivedFiniteModel": "8a1e954c3d65a24a4cb04aaa758bf13cba7a5437", "Sheaf.Paper.PodReindexingDerivedLimitModel": "8b1390fe309fa956f4383873af5ca653f9460b9c", "Sheaf.Paper.PodReindexingDerivedLimitProjection": "75869baf8c5be8b87cede56e375bc5319a3872d8", "Sheaf.Paper.PodReindexingDerivedReductionEvaluation": "068d09648acb10ecd2cb71435130989e2d9e5ce5", "Sheaf.Paper.PodReindexingDerivedUnit": "4c1a848c9fd0845a2bee37680b81a40478d2a32f"}, "results": {}, "time": "2026-10-28T08:20:56+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
