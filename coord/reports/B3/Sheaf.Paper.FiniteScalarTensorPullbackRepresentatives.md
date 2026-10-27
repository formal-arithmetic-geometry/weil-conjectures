## What changed

Replaced the item theorem's hole by an explicit representative-descent calculation.
The statement and all public imports are preserved. A general cancellation
lemma combines four representative equations, the unary pullback factor equation,
and the chain tensor square. Naturality moves the factor isomorphisms through the
tensor comparisons; cancellation then gives exactly the specified curried maps.
A general component equation for currying removes its identity maps before
specialization, avoiding expensive concrete category conversions.

Added `FiniteScalarOrdinaryPullbackComparison`: the ordinary scalar inverse-image
comparison is constructed as the inverse mate of the section-normalized right
comparison. The equality of the two constant-ring direct images is proved from
the coefficient adjunction. The comparison on complexes is constructed termwise.
The new module `FiniteScalarComplexTensorPullback` constructs the native
fixed-scalar comparison as a typed uncurried wrapper, with its
component equation proved in abstract categories. The proof uses that general
equation directly.
The intrinsic total comparison also receives a typed natural-transformation
wrapper with its component equation proved from the existing descent data. That
component specification uniquely determines the wrapper. No arbitrary witness is
selected.

Added `FiniteScalarFixedTensorPullbackNormalization`: proved the native fixed-scalar
left-derived tensor comparison's representative equation. This uses the existing
homotopy-category defining square, the identity-component quotient comparison,
the exact left-derived counit formula, and invertibility of K-flat tensorators.
The equation is proved for an abstract coefficient category and applied directly;
no redundant specialization recomputes the concrete tensor-category structures.

Added `RepresentativeTensorCube`, which proves the categorical cancellation
argument for abstract categories, and `FiniteScalarTensorRepresentativeData`,
which packages the specified scalar constructions and their existing representative
law. The record contains actual functors and maps, with no arbitrary choices.
The tensor functors themselves are explicit data in the record.
`RepresentativeTensorPullbackData` and `FiniteScalarTensorPullbackData` also package
the actual pullback maps. Four proved law adapters keep their type conversions in
separate modules; the item applies the categorical cube through that typed interface.
The fixed tensor presentations and pullbacks are shared parent records built over
abstract coefficients. Their normalization is checked before scalar specialization,
avoiding repeated concrete tensor-category conversions.

The shared signed-total functor and its component APIs avoid repeated kernel
conversion of concrete tensor functors. The representative, ordinary realization,
and fixed pullback wrappers retain exactly the existing component maps; their
component equations are proved before specialization.

Separated the two genuinely different unfinished steps into
`FiniteScalarPullbackRepresentativeFactors` (unary mate normalization, no tensors)
and `FiniteScalarTensorPullbackChainSquare` (ordinary chain square,
no derived objects or tensor models). The exact fixed-scalar pullback factors in
the unary module are constructed from existing natural isomorphisms.

## Proved and sorry left

Original holes closed syntactically: one,
`WeilConjectures.finiteScalarTensorPullback_onRepresentatives`. Its proof combines
existing representative declarations with two new strictly lower obligations;
this is a decomposition, not a claim of net hole reduction.

New proved declarations:

- `WeilConjectures.finiteScalarConstantPushforward_eq`;
- `WeilConjectures.finiteScalarTensorPullback_normalizationForCoefficients`;
- `WeilConjectures.finiteScalarIntrinsicComplexTensorPullback_app`;
- `WeilConjectures.finiteScalarComplexTensorPullbackForFunctor_app`;
- `WeilConjectures.finiteScalarFixedPullbackFactors_eq_counit`;
- `WeilConjectures.finiteScalarRepresentativeTensorCube`;
- `WeilConjectures.finiteScalarRepresentativeTensorIso_hom_app`;
- `WeilConjectures.finiteScalarRepresentativeTotalRealizationForFunctor_app`;
- `WeilConjectures.finiteScalarTensorRepresentativeData_normalization`;
- `WeilConjectures.finiteScalarSharedRepresentativeEquation`;
- `WeilConjectures.finiteScalarTensorSharedRepresentative_normalization`;
- `WeilConjectures.finiteScalarPullback_preservesRepresentatives`;
- `WeilConjectures.ScalarTensorPullbackData.tensorSquare`;
- `WeilConjectures.finiteScalarTensorPullback_fixedLaw`;
- `WeilConjectures.finiteScalarTensorPullback_intrinsicLaw`;
- `WeilConjectures.finiteScalarTensorPullback_factorsLaw`;
- `WeilConjectures.finiteScalarTensorPullback_chainLaw`;
- `WeilConjectures.finiteScalarFixedPullbackDataForCoefficients_law`.

All new definitions have actual constructed data and no holes.
The item's module has zero remaining holes. Two holes are added:

- `WeilConjectures.finiteScalarPullback_representative_factors`, node
  `lem-sf-finite-scalar-pullback-representative-factors`;
- `WeilConjectures.finiteScalarTensorPullback_chain_square`, node
  `lem-sf-finite-scalar-tensor-pullback-chain-square`.

The unary equation applies to every complex, including zero complexes; it asserts
no tensor compatibility. The chain equation applies before localization to the
specified ordinary mate and total tensor maps. Preservation of representatives is separately proved
from the existing flat-term K-flat preservation theorem and the native flatness
instance; it is not part of either remaining hole. Both statements include zero rings and empty schemes and add
no geometric, boundedness, or nonzero hypotheses.

Validation: all 24 sandbox modules compiled in import order through `lcompile.py`
with no profiling options. The final item compiled in 26.8 seconds and the chain
adapter in 6.5 seconds. Both named lower obligations are the only remaining sandbox
holes. A delivery compile first exposed a slow chain-law conversion; naming the
ordinary square over abstract categories removed that repeated conversion.

## No longer needed

The original public import `FiniteScalarTensorRealization` is preserved. The
existing `FiniteScalarTensorPullbackRepresentativeEquation` remains needed through
the equation adapters and `FiniteScalarTensorRepresentativeData`, which supplies
both realization representative equations.

The cancellation module publicly imports currying, full subcategories and the
fixed representative-data interface. Its scalar tensor-complex import is private
and supplies the proof's uncurrying component API. Redundant direct imports of tensor resolution, fixed representative data and the
normalization module were removed where another public import already supplies
them. These import refinements remove no mathematical obligation.

The item no longer cites `lem-sfb-constant-module-derived-projection-identification`
(`Sheaf.CategoryTheory.ConstantModuleDerivedProjectionIdentification`) as a proof
dependency. That theorem chooses general transport data; the current proof uses
the specified ordinary mate and actual representative equations directly. This
is a local dependency removal only, not a claim that its module is globally unused.

The general `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` is accessed through
the specialized canonical normalization and pro-etale descent-data declarations.
Its mathematical content remains needed, and no source-library declaration or
module is withdrawn. The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned generic constant-module projection identification does not directly
identify the specified concrete scalar comparison: its existential data do not
provide the needed equation for these maps. The missing compatibility divides
into an ordinary tensor square and a unary derived-mate normalization. The new
nodes record these actual substeps instead of repeating the original derived
tensor compatibility statement under another name.

No existing statement, shared definition, target, or source-library interface was
changed. No forced adaptation or change record is needed.

## New nodes

`def-sf-finite-scalar-ordinary-pullback-comparison`: the proved constant-direct-image
equality and constructed ordinary/complex inverse-mate comparisons.

`lem-sf-finite-scalar-pullback-representative-factors`: the constructed exact fixed
pullback factors and the unfinished unary derived-mate factor equation.

`lem-sf-finite-scalar-tensor-pullback-chain-square`: the unfinished ordinary signed
total tensor square and the separately proved preservation of the representative class.

`lem-sf-finite-scalar-fixed-tensor-pullback-normalization`: the proved native
fixed-scalar left-derived tensor representative equation.

`def-sf-finite-scalar-complex-tensor-pullback`: the constructed generic and
fixed-scalar signed-total tensor transformations, with their native component
equations proved; this isolates the concrete kernel conversions in a small file.

`lem-sf-representative-tensor-cube`: the proved general categorical representative
cancellation cube and its explicit representative-data record.

`def-sf-finite-scalar-tensor-representative-data`: the constructed record for the
specified scalar realization and its existing normalization equation.

`def-sf-finite-scalar-representative-total-tensor`: the shared raw signed-total
functor.

`def-sf-finite-scalar-representative-tensor-iso`: the existing K-flat representative
isomorphism assembled from its specified components on the shared functor.

`def-sf-finite-scalar-representative-total-realization`: the existing total realization
assembled on the shared source functor, with its component equation proved.

`lem-sf-finite-scalar-shared-representative-equation`: the proved change of total-complex
coordinates for a representative equation over abstract coefficients.

`lem-sf-finite-scalar-tensor-shared-representative-equation`: the proved scalar
representative equation using the shared tensor and the published ordinary map.

`def-sf-representative-tensor-pullback-data`: explicit pullback data and their four compatibility laws. All stored data and the categorical application are explicitly constructed.

`def-sf-finite-scalar-tensor-pullback-data`: the specified scalar pullback data. All stored data and the categorical application are explicitly constructed.

`lem-sf-finite-scalar-tensor-pullback-fixed-data-law`: fixed-coefficient normalization in the specified data. The theorem is proved from its existing normalization or lower stated obligation; no new hole is added.

`lem-sf-finite-scalar-tensor-pullback-intrinsic-data-law`: intrinsic normalization in the specified data. The theorem is proved from its existing normalization or lower stated obligation; no new hole is added.

`lem-sf-finite-scalar-tensor-pullback-factors-data-law`: unary mate normalization in the specified data. The theorem is proved from its existing normalization or lower stated obligation; no new hole is added.

`lem-sf-finite-scalar-tensor-pullback-chain-data-law`: ordinary chain normalization in the specified data. The theorem is proved from its existing normalization or lower stated obligation; no new hole is added.

`def-sf-representative-tensor-fixed-data`: fixed tensor presentations and their pullback law. Define a fixed tensor presentation by its localization q, representative class P, ordinary and derived tensor functors t and T, and the representative isomorphism r. Define pullback data by A, F, the exact factors f, preservation hA, and the two tensor maps mF and phiF. Their law is exactly the usual representative equation. All fields are explicit input data.

`def-sf-finite-scalar-fixed-tensor-data`: native fixed tensor presentation over abstract coefficients. Construct TensorFixedRepresentativeData for an abstract coefficient category B and scheme T using DerivedCategory.Q, the supplied K-flat representative class, the shared signed-total functor, the published derived tensor, and finiteScalarRepresentativeTensorIso. The definition is explicit and stores the actual existing maps.

`lem-sf-finite-scalar-fixed-pullback-data`: native fixed pullback data obey their representative law. Construct the fixed pullback record over abstract coefficients from ordinary upper star on complexes, its left derived functor, the supplied exact factors and preservation proof, and the specified ordinary and derived tensor comparisons. Its law follows by unfolding the small record projections and applying finiteScalarTensorPullback_normalizationForCoefficients with the supplied factors-to-counit equation. This proves the equation before concrete scalar specialization.

`lem-sf-finite-scalar-tensor-representative-data-normalization`: the proved representative normalization with both shared wrappers.
It is checked separately from construction of the scalar data record.

`def-sf-representative-tensor-ordinary-pullback-law`: the ordinary chain square as a shared
proposition over abstract categories. It names the same equation without repeatedly
expanding composite chain maps during scalar specialization; no hole is added.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarComplexTensorPullback": "3200b32d3e1edd4df86ab86b4dbf8829da146caf", "Sheaf.Paper.FiniteScalarFixedPullbackData": "7c4e826d43e2ac68a6688581694984f75e4161ba", "Sheaf.Paper.FiniteScalarFixedTensorData": "86202328c8f29f19f7ecc7aa55c2037e1005f2f5", "Sheaf.Paper.FiniteScalarFixedTensorPullbackNormalization": "7020a6e34ce9b057934074a764c7138e0962a8a7", "Sheaf.Paper.FiniteScalarOrdinaryPullbackComparison": "894f275ce4f15b15464519acb61f4dee8e47d6de", "Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors": "7a63b78a12743377f3b8cfe7791b55d2fb6da084", "Sheaf.Paper.FiniteScalarRepresentativeTensorIso": "615d337de83f7de0af5f974eeeca43f4ba290285", "Sheaf.Paper.FiniteScalarRepresentativeTotalRealization": "0c9777d0e1428cf106a96f29049463454723dc34", "Sheaf.Paper.FiniteScalarRepresentativeTotalTensor": "ce32e6918ac00bf9e2b5e6ecd6ae41605ca078db", "Sheaf.Paper.FiniteScalarSharedRepresentativeEquation": "71577486c6bbf1892aad4908f23b72ce474949ae", "Sheaf.Paper.FiniteScalarTensorPullbackChainDataLaw": "87eb4500c577d97336380dc154f2f932a38346fe", "Sheaf.Paper.FiniteScalarTensorPullbackChainSquare": "e9d84897b0cef5fc870b3afb66c3521a907327fa", "Sheaf.Paper.FiniteScalarTensorPullbackData": "a12fb42f1f960365edde7388c170eedd0a134b1a", "Sheaf.Paper.FiniteScalarTensorPullbackFactorsDataLaw": "bc64bf57b440c2f3bb5be9fb01b10cbe790754c2", "Sheaf.Paper.FiniteScalarTensorPullbackFixedDataLaw": "8fdeec443301d782ff3ad4b7956271068002cb32", "Sheaf.Paper.FiniteScalarTensorPullbackIntrinsicDataLaw": "05e3b10cc3d3f55f868576e7059ba4a8bdf24c0c", "Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives": "de539309003517ec06a3a39803d62d0547337f8a", "Sheaf.Paper.FiniteScalarTensorRepresentativeData": "e28a5a0af7cb3b096117aa1bd9ef0a8b7c3c3364", "Sheaf.Paper.FiniteScalarTensorRepresentativeNormalization": "ee5414c3db3f1a87391be778a8e0e440b7c4de23", "Sheaf.Paper.FiniteScalarTensorSharedRepresentativeEquation": "d973153a19b10449ba48da1f3dc6390e6d9451dd", "Sheaf.Paper.RepresentativeTensorCube": "4f89a198d5700ee04aaf15e501d26d237cb94c37", "Sheaf.Paper.RepresentativeTensorFixedData": "99fa35979344ef5fc910b9459923d7ce402bb020", "Sheaf.Paper.RepresentativeTensorOrdinaryPullbackLaw": "499d750240804bb4b8bb95cdbee7cc32afedf51b", "Sheaf.Paper.RepresentativeTensorPullbackData": "fcd57d7c58b67fef3c088e55df3b415eb5dc9b3c"}, "results": {"Sheaf.Paper.FiniteScalarTensorPullbackComparison": {"hash": "8fd1b4ca7281247287dd69a7a664c14ab6cdf5b6", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T02:25:33+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
