## What changed

Proved `WeilConjectures.PodReindexingCoherence.comparison_core_tensor_data_exists` in
`Sheaf.Paper.PodReindexingComparisonCoreTensorData`, with its signature and all three
structure fields unchanged. Two proved private helpers extend the existing
sectionwise ordinary tensor comparison to a natural signed total-complex comparison
and compute its pure-section formula. The derived comparison follows from the
supplied K-flat tensor models by the existing fully faithful representative
restriction and tensor-comparison descent theorems.

All added imports are private proof imports. The generic helper proofs follow the
existing private helpers of `AdicCochainTensorReindexing`; that specialization cannot
be imported here because it already reaches this item. Local reducibility attributes and a cached sheaf-composition witness keep large
coefficient constructions from expanding unnecessarily; the helpers retain the
item's coefficient-universe parameter. No structure-generated declaration is
suppressed. No other existing Lean module is changed. The item's DAG proof now records the actual constructions, and
its Lean module attachment loses an erroneous trailing period.

## Proved and sorry left

Closed one hole:
`WeilConjectures.PodReindexingCoherence.comparison_core_tensor_data_exists`
(node `lem-pod-reindexing-comparison-core-tensor-data`).
There are zero remaining holes and zero holes added or split off. Both new private
helpers and the private cached composition witness are proved. No existing
definitions or statements have been changed. The complete file compiled in
49.6 seconds with profiling enabled; profiling options are removed for delivery.

## No longer needed

No existing imports, nodes or modules are removed. Both previously declared proof
dependencies remain needed for their concrete definitions and Models comparisons.
The tensor argument uses no Hom-complex comparison, derived-Hom comparison, or
K-injective representative normalization. In particular it does not apply the
still-holed `podReindexing_tensor_hom_data` or `podReindexing_derived_hom_data`.
No module withdrawal is requested, and the unit's realized route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original node provided only a one-step construction plan citing definitions.
The existing ordinary sectionwise tensor comparison, total-extension machinery,
and representative descent prove this component package without a further split.
Its `lean.module` field incorrectly ended in a period, although `lean.file` already
pointed at the correct file; the attachment is corrected in this delivery.

The edge cases require no extra hypotheses: the sectionwise comparison works for
zero coefficient rings and empty schemes; the total extension uses all integer
bidegrees and applies to unbounded and zero complexes; the proof treats `some n`
and `none` uniformly, and transports the pure formula along any equality `p+q=k`.

## Related modules compiled before delivery

6 related module(s) compiled against this delivery by deliver3.py: 5 OK, 1 SLOW.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingComparisonCoreTensorData": "e9aab1e8d416bc71f8230ed8abb99dc069daf4ff"}, "results": {"Sheaf.Paper.PodReindexingComparisonCore": {"hash": "702efb07483195542fe0cb157619baf4688866c3", "status": "OK"}, "Sheaf.Paper.PodReindexingCompletedEvaluationReflection": {"hash": "2cd791a91f709fb971ab213014290bdd16b26db4", "status": "SLOW"}, "Sheaf.Paper.PodReindexingEvaluationShiftComposition": {"hash": "8fd374ba5ce1d67e1de2d3ac8ae43d8bff99d1a0", "status": "OK"}, "Sheaf.Paper.PodReindexingFiniteTensorComparison": {"hash": "0498c538c12b1a371a54334dc5d13d1a31f5b105", "status": "OK"}, "Sheaf.Paper.PodReindexingOrdinaryBraiding": {"hash": "524cec829965da2fa00b034690b87bad72670a4a", "status": "OK"}, "Sheaf.Paper.PodReindexingOrdinaryCurrying": {"hash": "0ccd61c6043126b871dda4ddb514700f505428bb", "status": "OK"}}, "seconds": 153, "time": "2026-10-28T12:09:44+0800", "transitive": 4, "version": 1}
```

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
