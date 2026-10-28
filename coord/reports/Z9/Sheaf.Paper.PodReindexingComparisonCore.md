## What changed

Filled `comparison_core_exists` by assembling three component packages. Added the
Hom-side component package, the tensor-chain/pure-tensor package, and the
K-flat tensor-model normalization package, each imported privately by the core
module. The core proof is a real record construction from these component
witnesses.

## Proved and sorry left

The core theorem `comparison_core_exists` is proved. Three strictly smaller
component existence theorems remain as intentional split-off sorries:
`comparison_core_hom_data_exists` (node
`lem-pod-reindexing-comparison-core-hom-data`),
`comparison_core_tensor_data_exists` (node
`lem-pod-reindexing-comparison-core-tensor-data`), and
`comparison_core_tensor_model_exists` (node
`lem-pod-reindexing-comparison-core-tensor-model`).

## No longer needed

No declared proof dependency was removed. The original dependency
`podReindexing_hom_resolution_model` is subsumed by the Hom component theorem;
the tensor and model declarations are retained through the corresponding
component packages.

## Where the brief, the DAG or earlier work was wrong

The original node treated the entire eight-field `Comparison` record as one
construction, although its Hom and tensor/model portions are independent data
packages. The delivery records that decomposition explicitly so the parent
proof is a genuine constructor application.

## New nodes

`lem-pod-reindexing-comparison-core-hom-data` records the Hom-side component
existence theorem.

`lem-pod-reindexing-comparison-core-tensor-data` records the tensor-chain and
pure-tensor component existence theorem.

`lem-pod-reindexing-comparison-core-tensor-model` records the K-flat tensor
model normalization theorem.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingComparisonCore": "702efb07483195542fe0cb157619baf4688866c3", "Sheaf.Paper.PodReindexingComparisonCoreHomData": "6928c8a35e7fc656c96c295069e2374ab05af7ef", "Sheaf.Paper.PodReindexingComparisonCoreTensorData": "41d2efff599aff07c4a6980adddb1b8e86515f8e", "Sheaf.Paper.PodReindexingComparisonCoreTensorModel": "29cf486967deda198ac163e0834967fcf924afad"}, "results": {}, "time": "2026-10-28T08:19:12+0800", "transitive": 0, "version": 1}
```

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
