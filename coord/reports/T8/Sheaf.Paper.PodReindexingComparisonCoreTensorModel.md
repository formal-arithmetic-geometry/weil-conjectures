## What changed

Corrected and proved `comparison_core_tensor_model_exists` by descending the
pure-normalized chain comparison through the product K-flat localization.
Its output now includes the derived tensor comparison it constructs. The
original `ComparisonCoreTensorModelData` structure and its exact normalization
field are unchanged.

Proved chain naturality on pure tensor generators, used the existing proved
K-flat preservation theorem and K-flat localization theorem, then descended
an explicit natural isomorphism made from `TY.comparison`, the factorization,
the chain comparison, and `TX.comparison`. The fully faithful preimage equation
and cancellation give the model equation. The two proved preliminary steps live
in separate modules so the final proof uses component equations without repeatedly
expanding the concrete sheaf comparison.

Adapted the sole caller `PodReindexingComparisonCore` to use this returned
tensor with its model equation. Its theorem still constructs exactly the
same `Comparison` with every original field. Updated both proof nodes and
corrected the item's malformed module attachment (trailing period).

Validation: the final `lcompile.py --all` completed with no warnings or errors.
The presentation comparison compiled in 56.6 seconds, the item in 49.2 seconds,
and the adapted parent in 4.3 seconds; the unchanged naturality result was reused
in that run (its standalone clean compile took 19.2 seconds). All files are
within the 60-second limit.

Change record: `coord/changes/pod-reindexing-core-tensor-normalized-choice.md`.

## Proved and sorry left

The original module had one hole, in
`WeilConjectures.PodReindexingCoherence.comparison_core_tensor_model_exists`
(node `lem-pod-reindexing-comparison-core-tensor-model`). Its old universal
statement was false and has been corrected with the caller adapted; the
corrected normalized-choice theorem is fully proved. This is a statement
repair with a complete proof, not a proof of the old false universal claim.
There are zero holes left in the item and zero holes added by the delivery.
No unproved intermediate statements were split off. The proved helper
`WeilConjectures.PodReindexingCoherence.tensor_chain_naturality`
(node `lem-pod-reindexing-tensor-chain-naturality`) is in its own module.
The fully proved presentation step
`WeilConjectures.PodReindexingCoherence.tensor_presentation_comparison`
(node `lem-pod-reindexing-tensor-presentation-comparison`) records the explicit
three-factor natural isomorphism and its components. Its K-flat lift is an actual
construction from the existing preservation theorem. The adapted parent remains proved.

Existing component hypotheses, including the still-unproved tensor-data
existence theorem used by the parent, remain existing work items. No new
assumption was added to `comparison_core_exists` or to the targets.

## No longer needed

The independent `tensor` input of the old false theorem is removed. In the
parent the arbitrary `t.tensor` field is unused; its tensor is chosen by
localization with its representative equation. The existing tensor-data
module remains needed for `tensorChain` and `tensorChain_pure`; no module or
node is withdrawn. Its preliminary derived tensor field could be pruned in
a future coordinated simplification of that structure and its other users.

The direct public import of `PodReindexingCoherenceData` is replaced by its
public importer `PodReindexingComparisonCoreTensorData`, needed by the new
signature. Every new proof import is used. The two original definition
proof dependencies remain used; no originally listed dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The last split mistakenly asserted compatibility for independently arbitrary
chain and derived tensor isomorphisms. Negating just the latter refutes it on
the coefficient tensor unit over F_3 on a nonempty point. The canonical
comparison required by the blueprint must be constructed together with its
normalization. The correction retains exactly that canonical normalization
and the unchanged parent conclusion; it does not add an assumption to the
parent. Empty schemes and zero complexes are covered automatically by the
same localization construction, as are completed coefficients and all finite
stages, with no boundedness assumption.

The item's `lean.module` had an erroneous trailing period, which prevented
an exact module-name search from finding it. The parent's DAG proof still
named older dependencies and did not record its actual three component
imports. Both records now follow the Lean argument. The only actual caller
is adapted, and the statement-change record audits the absence of other DAG
citers. The current unit `sk-def-weil` has no realized steps; this repair
implements the same tensor part of the cited dual-Tate proof.

## New nodes

`lem-pod-reindexing-tensor-chain-naturality`, in
`Sheaf.Paper.PodReindexingTensorChainNaturality`, is fully proved. It records
the pure-generator naturality step, strictly below the localization argument.
It is a self-contained preliminary step, separated from the concrete comparison
construction and the abstract descent calculation to control unfolding costs.
It adds zero holes. Change record:
`coord/changes/pod-reindexing-core-tensor-normalized-choice.md`.

`lem-pod-reindexing-tensor-presentation-comparison`, in
`Sheaf.Paper.PodReindexingTensorPresentationComparison`, proves the explicit
comparison on the K-flat presentation and its component formula. It is the
construction before the product-localization descent, strictly below the item's
derived normalization. It and its explicit full-subcategory lift are fully
implemented and add zero holes. Separating its component formula prevents the
main proof from expanding the concrete composite repeatedly. The same change
record above covers the repair and its proof modules.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingComparisonCore": "2c9d168188cee161353b70b4e8532ce41bdcbee0", "Sheaf.Paper.PodReindexingComparisonCoreTensorModel": "5f815ec76f760b16adc308cca6477e11aed42841", "Sheaf.Paper.PodReindexingTensorChainNaturality": "e56e7eadba4de0f87116da808dce6fdbb685db04", "Sheaf.Paper.PodReindexingTensorPresentationComparison": "2d56fb1a0ca00de9eac8d702e41d79055a36bacb"}, "results": {}, "time": "2026-10-28T12:40:04+0800", "transitive": 0, "version": 1}
```

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
