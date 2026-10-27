## What changed

Filled `WeilConjectures.OpenFactorCoherence.tensorCompletionModel_nonempty` in
`Sheaf.SixFunctors.TensorCompletionModelExistence` using the existing ambient
operation comparison. The ordinary tensor is its recorded tensor, with the
representative comparison restricted to flat-term K-flat complexes. The chain
augmentation is constructed from the natural quotient Roos unit and the
normalized strict tensor-tower isomorphism. Its two coordinates follow from
`tensorOperationUnit_coordinates`, `augmentation_existsUnique`, and
`tensorTowerModel`. Precomposing the ambient tensor augmentation equation with
the ordinary representative isomorphism gives the required square by cancellation.

Added proof-only imports of `IntegralAmbientOperationModels`,
`TensorQuotientChainData`, and `TensorOperationUnitNormalization` to the item.
The latter two are new modules of this packet. The data module constructs the
ordinary model, good-class inclusion and chain, with proved naturality and
component identities; the coordinate module proves their normalization.
After profiling the original proof, making the data irreducible and reducing
record projections and whiskering components explicitly, these self-contained
parts were extracted to keep each file within the compile limit. Every statement
in both new modules is proved. Instance erasures are scoped to individual
commands and do not change imported instance attributes for consumers. The data
module's proof-only `import all IntegralDerivedOperationsOnSlices` accesses its
proved Roos-unit naturality lemma through a public theorem wrapper.

Updated the assigned node's proof, proof dependencies, and proof origin, and
added nodes for the two new modules. No existing public signature, definition,
public import, or target changes. No shared-module adaptations are required. The three-module sandbox compile
passed on 2026-10-27; the temporary profiling options were then removed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.OpenFactorCoherence.tensorCompletionModel_nonempty`
(node `lem-sf-tensor-completion-model-existence`).

There are zero remaining holes in the item and zero holes added elsewhere.
No unfinished statements were split off. Every private helper is proved. The
public coordinate lemma
`WeilConjectures.OpenFactorCoherence.tensorOperationUnit_normalized`
(node `lem-sf-tensor-operation-unit-normalization`) and all the data module's
naturality and component lemmas are proved.

## No longer needed

None. No existing import, module, or node is withdrawn. The proof does not invoke
the constructibility/completeness assertion `constructibleTensorCompletion`;
its module remains necessary for the specified total tensor, pure sections and
boundary. The existing ambient comparison supplies the required isomorphism on
all derived inputs, so no additional constructibility argument is needed here.
The original dependencies remain needed through the new data module, and the
unit route is unchanged. The temporary redundant `import all` of the slice
module was removed from the coordinate module before delivery.

## Where the brief, the DAG or earlier work was wrong

The planned ambient-comparison route is valid. The current ambient API shares
its operations in `ambientPackage`; transporting along the proved
`ambientPackage_eq` is required before reading its normalization in the concrete
interface. The ordinary K-flat predicate and the independent-coefficient
predicate agree by the existing equivalence at the present universes.

## New nodes

`def-sf-tensor-quotient-chain-data`, realized in
`Sheaf.SixFunctors.TensorQuotientChainData`: explicit ordinary tensor data and
the natural quotient-chain augmentation, with the proved component identity.
All constructions reuse the existing operations, without arbitrary choices.

`lem-sf-tensor-operation-unit-normalization`, realized by the proved theorem
`WeilConjectures.OpenFactorCoherence.tensorOperationUnit_normalized` in
`Sheaf.SixFunctors.TensorOperationUnitNormalization`: a chain with the recorded
operation-unit components has the pure-section and zero shifted coordinates.
It assumes neither constructibility nor scheme compactness. No change records
are needed because no other existing module or node was changed.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
