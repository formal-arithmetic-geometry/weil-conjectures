## What changed

Replaced the assigned hole in
`WeilConjectures.podReindexingTensorCoefficientTransition_tensor` by descent from
its good constructible representatives. Its signature is unchanged. The proof
uses `CategoryTheory.functorSquareTowerDescent`, the specified tensor Model and
Naturality laws, scalar normalization, and exact-derived comparison factors.

The representative API constructs good-complex scalar functors, localization
comparisons, tensor Roos maps and the termwise ordinary coefficient transition.
Every construction is explicit; none chooses data from a mere existence theorem.
The generic theorem `WeilConjectures.podCoefficientExactSquareChain` proves how a
chain square descends through the specified exact-derived factors. Reindexing,
scalar, mixed and coefficient representative normalization steps are proved in
separate modules. Explicit functor associators avoid expensive definitional
comparisons, and a private component lemma cancels them before model expansion.

One remaining theorem isolates the tensor square on the actual Roos
representatives. Its conclusion has no completed-tensor comparison or tensor Model clause; it is
the mixed square of the actual Roos chain maps and their localization factors.
Its docstring explains the quotient-generator, signed-total, transition and
Roos-coordinate calculation, followed by the proved exact-derived factor step.

Server checks compiled the original theorem in 17.9 seconds and the four
named-diagram normalization modules in 7.3–26.5 seconds, with no warnings.
The representative modules also passed their individual checks. Profiling
settings have been removed. An unused private pasting helper was removed from
the representative API; its used copy remains beside the mixed normalization.

## Proved and sorry left

The assigned module has zero `sorry`. The removed hole is
`WeilConjectures.podReindexingTensorCoefficientTransition_tensor`. It is reduced to one
remaining theorem:
`WeilConjectures.podTensorMixedRepresentativeChainSquareDiagram`, node
`lem-pod-tensor-chain-square-diagram`.

One upper hole removed, one earlier hole added: this is a decomposition, with
zero net holes closed. All other new theorems and all definitions are complete.

## No longer needed

No existing module is withdrawn and no original public import is removed.
The old plan's separate appeals to
`lem-weil-finite-free-completed-scalar-comparison` and
`lem-trf-integral-pullback-comparison-realization` are not used by the assigned
proof: its normalization laws already supply those representative equations.
These nodes and their modules remain used elsewhere. The general tower-descent
theorem replaces a repeated localization argument. No blueprint unit statement
or realized step is bypassed. No unused intermediate chain-square theorem is
left in the delivery.

## Where the brief, the DAG or earlier work was wrong

The ordinary transition core does not contain the mixed tensor square on Roos
representatives. The earlier plan leaves that calculation implicit. The remaining
node states the precise earlier calculation on the fixed maps. Identity scheme
and coefficient maps, zero complexes and empty sites require no exceptional
case: the same generator and cone-coordinate equations apply. No existing
statement or definition is changed. The helper modules separate genuine steps
of the argument so that each kernel check can meet the file limit. Named diagram
definitions retain their checked functor types, avoiding repeated conversion of
large concrete module-category expressions.

## New nodes

`def-pod-reindexing-tensor-chain-maps`, in
`dag/nodes/sec-poincare-duality/`, records the explicit tensor Roos reindexing map
and the termwise ordinary coefficient transition. Both definitions are complete.

`lem-pod-coefficient-exact-square-chain-descent`, in the same directory, records
the proved generic exact-derived chain-square theorem and the representative API.
Its proof moves comparison factors by naturality and uses the given chain equation.

`lem-pod-tensor-reindex-normalization`, in the same directory, records the proved
reindexing representative normalization, obtained from the tensor Model clause.

`lem-pod-tensor-scalar-normalization`, in the same directory, records the proved
scalar representative normalization from the prescribed scalar comparison.

`lem-pod-tensor-mixed-normalization`, in the same directory, records the proved
pasting of scalar normalization, target-field tensor Model and tensor naturality.

`lem-pod-tensor-representative-square`, in the same directory, records the proved
coefficient square from exact-derived composition and natural-isomorphism factors.


`def-pod-tensor-descent-diagram`, in `dag/nodes/sec-poincare-duality/`,
records the explicit named diagram components. All data is constructed.

`lem-pod-tensor-reindex-normalization-diagram`, in the same directory,
records the proved conversion from `lem-pod-tensor-reindex-normalization` to the
corresponding named-diagram compatibility. No hole is introduced.

`lem-pod-tensor-scalar-normalization-diagram`, in the same directory,
records the proved conversion from `lem-pod-tensor-scalar-normalization` to the
corresponding named-diagram compatibility. No hole is introduced.

`lem-pod-tensor-mixed-normalization-diagram`, in the same directory,
records the proved conversion from `lem-pod-tensor-mixed-normalization` to the
corresponding named-diagram compatibility. No hole is introduced.

`lem-pod-tensor-representative-square-diagram`, in the same directory,
records the proved conversion from `lem-pod-tensor-representative-square` to the
corresponding named-diagram compatibility. No hole is introduced.

`lem-pod-tensor-chain-square-diagram`, in the same directory, is the single
remaining obligation: the mixed square of the fixed Roos representative maps.
Check quotient generators, signs and transitions, then both Roos coordinates;
apply the proved exact-derived factor lemma. It is strictly before tensor
normalization and faithful descent. No redundant component square is retained.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingScalarTensorChainSquare": "4f1e70161cf78ecfef7a0ed385a24582814a0de9", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionChainSquareDiagram": "6f1d7ee95202f67356c3f5e5f5ecd281c289a9f4", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionDescentData": "3eb2b819c125ddd1636ca357aa675f91ea37bc63", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionMixedNormalization": "08c46ddbcd26d3597a1d3b1af6183d5b4a967097", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionMixedNormalizationDiagram": "2e768d90018487354b4dce4caade2a34b795a96a", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionReindexNormalization": "64e15eab36a4edd3a95f7c49aa922335e97db1cb", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionReindexNormalizationDiagram": "8b94c344f953e99d77e54d0345d4f3d2c3d1ce86", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionRepresentativeSquare": "6410aeeed2910f903759c18ae86fafee1c5c15e7", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionRepresentativeSquareDiagram": "38cd70fb6391b5990962c9dd324f947e376bf406", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionScalarNormalization": "93d075bb89a70948ec5c2b4e2546926b56a7f371", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionScalarNormalizationDiagram": "4d6cb0981af5704d36c1784b9c26d06b2f240e27", "Sheaf.Paper.PodReindexingTensorCoefficientTransitionTensor": "0db7b60beb57f25aca24aee20f8121e26890a0ab", "Sheaf.Paper.PodReindexingTensorDescentDiagram": "ddd39e02ed16cb4019a65a54e8be9959daceac3e"}, "results": {"Sheaf.Paper.LisseShortComplexCommonStageExactness": {"hash": "18a61169a26d6e303a10b142bae45c5b5e926f72", "status": "OK"}, "Sheaf.Paper.PodReindexingCompletedEvaluationReflection": {"hash": "2cd791a91f709fb971ab213014290bdd16b26db4", "status": "OK"}, "Sheaf.Paper.PodReindexingTensorCoefficientTransition": {"hash": "9bf9dc2f5757ae32029131de124af21585a47dfd", "status": "OK"}}, "seconds": 148, "time": "2026-10-28T12:31:16+0800", "transitive": 2, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
