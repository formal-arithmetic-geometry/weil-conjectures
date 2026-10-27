## What changed

Replaced the sole proof hole in `Sheaf.Paper.PodReindexingTensorAugmentationSquare`
by a categorical assembly proof. Its statement and existing public imports are unchanged.
The proof expands the specified augmentation, uses naturality of the limit comparison,
transports the actual adjunction unit with `PodCompletionReindex.Unit`, and applies
naturality of the target unit. A proved abstract helper assembles the two squares by cancellation and naturality;
a private specialization evaluates it at the fixed augmentation.

Added two modules separating the independent normalization calculations:
`Sheaf.Paper.PodReindexingReductionTensorSquare` works before the total limit and
contains no completed tensor comparison; `Sheaf.Paper.PodReindexingTensorLimitModel`
identifies completed tensor isomorphisms and contains no ordinary tensor comparison
or augmentation. The system tensor map is constructed from the existing canonical
comparison by equality transport. The equality of the sequence pullback presentations
and the whole-system adjunction-mate formula for the inverse reduction comparison
are proved, with no new chosen data. A named definition for the transported ordinary
tensor arrow and its proved defining equation keep equality transport out of repeated
type comparisons. A second proved wrapper displays the existing completed tensor
realization in the same coefficient calculus. Both wrappers have proved defining
equations and introduce neither choices nor proof holes.

`PodTensorAugmentationFrame` shares the categories, functors and actual arrows used
by both squares. `podReindexingTensorFrame` constructs it directly from the existing
maps and proves its sole compatibility field from `hA.Unit`. Neither tensor
compatibility is a field of the frame. This keeps the same concrete category types
throughout the assembly and avoids repeated expensive unfolding of derived categories.

Verification: all three modules compile individually against the supplied project
artifacts, in import order (8.2 s, 3.5 s, 4.8 s). The original theorem signature is
verbatim unchanged; the two new modules contain the only two remaining holes.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.podReindexing_tensor_augmentation_square`
(node `lem-pod-reindexing-tensor-augmentation-square`) by decomposition.
The item module has zero holes. Added two holes, each exactly a named public theorem:

- `WeilConjectures.podReindexing_reduction_tensor_square`
  (`lem-pod-reindexing-reduction-tensor-square`): the tensor/reduction equation in
  the coherent system category, for arbitrary ambient derived inputs.
- `WeilConjectures.podReindexing_tensor_limit_model`
  (`lem-pod-reindexing-tensor-limit-model`): the completed tensor comparison is the
  normalized limit of the coherent tensor comparison, on constructible inputs.

This is a decomposition, not a net hole reduction: one hole closed, two added.
The two remaining statements are independent parts of the representative argument:
the first has no `T`, `hT` or augmentation, and the second has no `c`, `h` or augmentation.
Neither is the original square with its hypotheses repackaged.

The additional helpers `podReindexing_sequence_pullback_eq` and
`podReindexing_reduction_inv_mate` are completely proved. The latter fixes a
whole-system arrow through the adjunction Hom bijection; finite derived evaluations
are not used to infer equality of arbitrary derived arrows.

## No longer needed

No existing import was removed and no module is withdrawn. The assembly theorem
no longer directly uses K-flat resolutions, quotient-generator calculations, or Roos
coordinate calculations. Those remain needed by the two new normalization lemmas;
no transitive pruning of their nodes or modules is claimed.

Its proof dependencies are now the two new lemmas and
`def-pod-completion-reindex-models`, whose `Unit` law the proof uses. The previous
direct proof dependencies `def-coef-derived-system-calculus-data`,
`def-pod-completion-tensor-normalization`,
`lem-pod-reindexing-evaluation-shift-composition` and `lem-pc-kflat-resolution`
are not direct proof steps of the assembly. Their definitions and representative
normalizations are retained in the statement or the new lower proofs as appropriate.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original single proof step grouped two different
representative normalization squares together with an elementary adjunction-unit
calculation. This delivery separates them and formalizes the latter calculation.
The related `IntegralOrdinary.reductionTensorPullback` and
`IntegralOrdinary.tensorPullback_augmentation` use different specified functors,
tensor models and normalization predicates; they do not directly instantiate to
this theorem for arbitrary supplied `A`, `T` and `c`.

Edge cases were checked in the proposed statements: the reduction square uses
arbitrary unbounded ambient inputs; the limit square retains the original
constructible domain. The constructions use the same normalized maps on zero
complexes, identity isomorphisms and the empty scheme. No completeness of an
ordinary tensor or finite Tor dimension was added.

## New nodes

`lem-pod-reindexing-reduction-tensor-square` records the coherent tensor/reduction
square and the construction of the equality-transported system comparison, in
`Sheaf.Paper.PodReindexingReductionTensorSquare`. Its source is blueprint dual-Tate
compatibility Steps 2 and 4 and Stacks 07A4/0941. The file also proves that the inverse
reduction comparison is the whole-system adjunction mate fixed by the unit law.

`lem-pod-reindexing-tensor-limit-model` records the independent normalized limit
realization of completed tensor reindexing in
`Sheaf.Paper.PodReindexingTensorLimitModel`. Its source is the same blueprint steps,
with the strict tensor and two-coordinate Roos normalizations of Stacks 07A4/08TC/0941.
Both nodes retain the parent's chapter, unit and blueprint ancestry. No existing
module besides the item and no node of another existing module is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingReductionTensorSquare": "5d319dce971fb8068cf45dfb1bb25c9f5b856453", "Sheaf.Paper.PodReindexingTensorAugmentationSquare": "8f39287d3aa0bb5e214ba8278bc7f7c44144da86", "Sheaf.Paper.PodReindexingTensorLimitModel": "c6b0edb3fd39bce7253501a50e9a1668046d9dcd"}, "results": {"Sheaf.Paper.PodReindexingCompletedEvaluationReflection": {"hash": "da55a69996fc689ebc7f955006772d79ffe1678b", "status": "OK"}}, "seconds": 61, "time": "2026-10-28T04:08:10+0800", "transitive": 0, "version": 1}
```

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
