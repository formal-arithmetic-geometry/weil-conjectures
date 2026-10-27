## What changed

Proved finiteScalarTensorPullbackComparison from a constructed, uniquely normalized
single-site tensor realization and the tensor-pullback equation on flat-term K-flat
pairs. The proof forms the two natural transformations, resolves both arbitrary derived
inputs, and uses naturality and cancellation to extend the representative equation.
The uncurrying and extension calculations are proved in private abstract-category
helpers, then specialized to the pro-etale coefficient categories.
The original theorem statement is unchanged.

FiniteScalarPullbackComparison contains the two original definitions with unchanged
names, signatures and bodies. The item publicly re-exports it. This avoids an import
cycle in the representative lemma. FiniteScalarTensorComplex constructs the ordinary
sheafification tensor map and its signed total. FiniteScalarTensorResolution proves
preservation of the resolving class,
fully faithful resolving restriction and the fixed localization tensor representative.
FiniteScalarTensorDescent constructs the generic derived tensor isomorphism directly
from the unique normalized witness of the proved tensorComparisonDescent theorem.
This retains the actual normalization without repeating its large concrete equation
in a second declaration type.
FiniteScalarTensorRealization specializes the target first to intrinsic ring sheaves,
then specializes to the scalar coefficient category and the intrinsic constant ring. Its specialization API accepts the ordinary
tensor comparison and forms the signed total before substituting the constant ring.
The construction is grouped into ordinary and total comparison, resolving models,
generic descent and specialization. The files use the native coefficient and additive
structures of module sheaves, complexes and functor categories. The descent
API includes the actual component normalization equation, so its users need not unfold
the construction's unique choice.

Validation: all seven packet modules compile through lcompile.py. The construction
files take at most 41.3 seconds in the final grouped build; the representative statement
takes 9.4 seconds and the final theorem 7.2 seconds. The unchanged direct importer
FiniteScalarProperProjectionPresentation compiles against the packet in 5.3 seconds;
its temporary copy was removed before delivery. The first delivery check caught an
incorrect stored signature caused by a name-prefix match in the metadata refresh;
the node now records the exact finiteScalarTensorRealization signature.

## Proved and sorry left

Closed the original hole WeilConjectures.finiteScalarTensorPullbackComparison (1 of 1).
Added one hole: WeilConjectures.finiteScalarTensorPullback_onRepresentatives, node
lem-sf-finite-scalar-tensor-pullback-representatives. This is a decomposition: one original
hole closed and one new hole added. The remaining equation fixes the constructed tensor
data and is only
on resolving cochain pairs; it neither chooses tensor isomorphisms nor extends the
square to arbitrary derived inputs. All tensor construction and extension steps are
proved in Lean. No sorry occurs in any definition.

## No longer needed

Removed the four redundant direct public imports ProEtaleCanonicalTensorPullback,
FiniteRingCompactSupportProjectionMap, ProjectionMapMate and InverseMateEquivalence
from the item: they are publicly re-exported through FiniteScalarPullbackComparison.
The original SfIntrinsicRealizationTransport public import is likewise re-exported
through that new module. These imports and their declarations remain available to all
existing consumers.

Removed the redundant KFlat import from FiniteScalarTensorComplex. The flat resolution
module is now imported privately by FiniteScalarTensorResolution and the item, where
its existence theorem is used; it is not needed by the complex construction's public API.

The new single-site construction does not directly use
lem-sfb-constant-scalar-restriction-tensor (Sheaf.CategoryTheory.ConstantScalarRestrictionTensor)
or its generic reverse scalar-restriction DerivedComparison package: it constructs the
actual associated-module realization
comparison and applies tensorComparisonDescent. The residual compatibility proof still
uses the ordinary and derived adjunction normalization route. No global module or node
is claimed pruned. The blueprint unit's statement and route remain in place.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The generic constant-module comparison uses restriction
in the reverse direction and generic tensor data, so it is not a direct specialization
to the specified realization and arbitrary supplied intrinsic tensor models. The
existing intrinsic total-tensor theorem provides objectwise Nonempty chain isomorphisms;
its concrete natural construction is private. The delivery reconstructs that signed
total natural isomorphism explicitly instead of choosing arbitrary witnesses.

## New nodes

- def-sf-finite-scalar-pullback-comparison: the two unchanged pullback definitions, moved
  to their own module so the residual square can refer to them without a cycle.
- lem-sf-finite-scalar-tensor-complex: the proved ordinary and signed-total natural tensor
  isomorphisms for the specified realization.
- lem-sf-finite-scalar-tensor-resolution: preservation of the resolving class, fully
  faithful resolving restriction, and inverse localization tensor representative.
- lem-sf-finite-scalar-tensor-descent: the proved abstract coefficient tensor
  descent, including its actual component normalization.
- lem-sf-finite-scalar-tensor-realization: the proved derived tensor realization with
  unique representative normalization.
- lem-sf-finite-scalar-tensor-pullback-representatives: the remaining scalar tensor square
  on flat-term K-flat pairs for the constructed tensor data, with its source and complete
  proof in words.

Change record: coord/changes/finite-scalar-tensor-pullback-definitions.md.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
