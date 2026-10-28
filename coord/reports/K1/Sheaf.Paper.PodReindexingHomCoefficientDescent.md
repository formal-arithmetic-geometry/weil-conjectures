## What changed

The item `Sheaf.Paper.PodReindexingHomCoefficientDescent` and its existing node
`lem-pod-reindexing-hom-coefficient-descent` are changed. Three fully proved helper
modules and their nodes are added, as described below.

- Proved `ambient_coordinates` by specializing the existing finite-free coordinate
  and tensor interfaces to the recorded scalar extension. Uniqueness identifies
  the tensor comparisons with the prescribed ones. The supplied adjunctions,
  unit formula and chain-transpose normalization assemble the required
  `ScalarDerivedPair`, with its original extension and derived functors.
- Proved `common_compositor_existsUnique`. Tensor-product induction proves
  naturality of the rational compositor; representative induction and cancellation
  of the comparison isomorphisms prove common-stage naturality. Equality-only
  transport gives the compositor for `commonPullback`, and componentwise
  extensionality gives uniqueness. The private naturality proof follows the
  already proved argument in `SemilinearFieldOperationLifts`, which cannot be
  imported here because its dependency chain imports this item.
- Added private proof imports for `PodCommonStageCompositorNaturality`,
  `PodFiniteScalarTensorNormalization` and `ExactScalarDerivedPair`. The first
  supplies naturality; the second extends the prescribed tensor normalization
  to arbitrary K-flat inputs; the third constructs the scalar pair from the
  normalized ordinary and derived adjunctions. All three statements are proved.
- Updated the existing node's proof and proof origin to record these arguments,
  and added the three proved helpers as proof dependencies. Their nodes
  explicitly cite the operation normalization, finite-free tensor and scalar-pair
  interfaces used by their proofs. No existing public signatures,
  definitions, attributes or public imports are changed.

The scalar argument uses arbitrary unbounded inputs and the supplied finite-free
basis, including rank zero. It adds no constructibility or perfectness condition.
The compositor argument treats arbitrary localized arrows and arbitrary common-
stage representatives, without assuming faithful scalar transition functors.

## Proved and sorry left

Closed 2 of the 20 holes in the current item source, with no holes added and no
split-off statements:

- `WeilConjectures.PodCoefficientDescent.ambient_coordinates`
- `WeilConjectures.PodCoefficientDescent.common_compositor_existsUnique`

The following 18 existing holes remain unchanged. Each belongs to
`lem-pod-reindexing-hom-coefficient-descent`, with its original sourced proof
plan and docstring:

- `WeilConjectures.PodCoefficientDescent.ambient_reindex_scalar`
- `WeilConjectures.PodCoefficientDescent.ambient_scalar_chain`
- `WeilConjectures.PodCoefficientDescent.rational_transpose_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_signedShift_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_comparison_existsUnique`
- `WeilConjectures.PodCoefficientDescent.integral_existsUnique`
- `WeilConjectures.PodCoefficientDescent.integral_scalar`
- `WeilConjectures.PodCoefficientDescent.rational_scalar`
- `WeilConjectures.PodCoefficientDescent.integral_evaluation_transposition`
- `WeilConjectures.PodCoefficientDescent.rational_evaluation_transposition`
- `WeilConjectures.PodCoefficientDescent.rational_composition`
- `WeilConjectures.PodCoefficientDescent.rational_pullbackShift_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_signed_shifts`
- `WeilConjectures.PodCoefficientDescent.common_evaluation_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_comparison_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_evaluation`
- `WeilConjectures.PodCoefficientDescent.common_transpose_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_composition`

The three new auxiliary theorems are fully proved, with no holes:

- `WeilConjectures.PodCoefficientDescent.commonStagePullbackComposition_naturality`
- `WeilConjectures.PodCoefficientDescent.scalarClosedTensor_allKFlat`
- `SheafOfModules.exactScalarDerivedPair`

They isolate naturality, tensor normalization and normalized adjunction assembly,
respectively. None restates the parent coordinate or compositor conclusion.

Validation: the compositor-only version compiled in 39.2 seconds and the
coordinate argument compiled in isolation. Their combined inline version had
no proof errors but took 83.2 seconds. After keeping the rational functor abstract
locally, the proved naturality, tensor normalization and pair assembly steps were
factored into separate modules. The helper compiles take approximately 14, 20 and
4 seconds respectively. The final item compiles in 43.5 seconds, with no compiler
errors or warnings (lcompile result 3ff20e974d3fea35015fda84). All existing named
signatures and public imports match the current shared source. All four DAG node
records have known dependencies, and every proof-step use is in proof_deps. This is a
partial proof delivery: the remaining holes are not claimed as closed.

## No longer needed

None. No imports, modules or nodes are withdrawn. The two proofs use the existing
planned finite-free coordinate/tensor and rational/common-stage operation
interfaces. The original dependencies of the remaining obligations stay needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The prescribed common-stage
compositor is initially a family of component isomorphisms, so its naturality has
to be proved before constructing a natural isomorphism. Equality transport alone
does not supply that missing naturality. The proof now gives that argument.

The current source and queue contain 20 holes, rather than the older count of 21
in an earlier progress note. The reported denominator is the actual source count.


## New nodes

`lem-pod-common-stage-compositor-naturality`, realized by the proved theorem
`WeilConjectures.PodCoefficientDescent.commonStagePullbackComposition_naturality`
in `Sheaf.Paper.PodCommonStageCompositorNaturality`, records naturality of the
prescribed component compositor. Its proof uses tensor induction and the integral
compositor equation, followed by common-stage representative induction and
cancellation of the operation comparisons. This is a genuine step of existing
proof Step 14 and is completely proved. The zero arrow, sums, identity scheme
maps and empty schemes require no extra hypothesis; the proof uses the given
operation equations uniformly. It adds zero holes. The unit route is unchanged.
There are no definition changes, forced adaptations or change records.

`lem-pod-finite-scalar-tensor-all-kflat`, realized by the proved theorem
`WeilConjectures.PodCoefficientDescent.scalarClosedTensor_allKFlat` in
`Sheaf.Paper.PodFiniteScalarTensorNormalization`, identifies the existing generic
tensor data with the prescribed scalar comparisons on every K-flat pair. The
identifications follow from the generator and good-representative uniqueness
interfaces. Zero complexes and arbitrary unbounded K-flat pairs are covered.

`lem-pod-exact-scalar-derived-pair`, realized by the proved theorem
`SheafOfModules.exactScalarDerivedPair` in
`Sheaf.Algebra.Homology.ExactScalarDerivedPair`, assembles the exact functor's
scalar pair from the ordinary unit and derived chain-transpose equations. It
constructs the original functors and adjunction, with no arbitrary witness or
coordinate assumption. Both auxiliary statements are strict parts of Step 2,
fully proved, and add zero holes. The unit route is unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Algebra.Homology.ExactScalarDerivedPair": "7aced24c516382049eb5727b23ca5beb4e5dbe81", "Sheaf.Paper.PodCommonStageCompositorNaturality": "1518b88eb26ca5542fc1fec38a56b7266ff35584", "Sheaf.Paper.PodFiniteScalarTensorNormalization": "46f444e43b2fa561216346b834435faa69487c10", "Sheaf.Paper.PodReindexingHomCoefficientDescent": "9689050e964af829992911358e320fa4ee5c5ac1"}, "results": {}, "time": "2026-10-28T08:39:42+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
