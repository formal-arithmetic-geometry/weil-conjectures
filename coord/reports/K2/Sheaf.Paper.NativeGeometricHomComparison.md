## What changed

Filled `AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_derivedHomComparison`
without changing its signature or public imports. The proof extracts the actual native
closed comparison, applies its Hom isomorphism and native-model isomorphism, and then
transports the ordinary closed adjunction through the coefficient equivalence.
A proved private categorical helper constructs the latter isomorphism using
`conjugateIsoEquiv` on two composite adjunctions, followed by the equivalence's unit
and counit. All chosen equivalence data are used only in theorem proofs.

Added the proof imports `Sheaf.Paper.NativeCoefficientTensorComparison`,
`Sheaf.Paper.NativeScalarForgetting`, and `Mathlib.CategoryTheory.Adjunction.Mates`.
Updated the item's node to this argument. Added one new module and node for the
coefficient equivalence's ordinary derived-tensor comparison. No existing definition,
statement, consumer, source-library module, or public import changed.

## Proved and sorry left

Original item: one hole. Closed the body of
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeGeometricForget_derivedHomComparison`
(node `lem-sf-native-geometric-hom-comparison`). The combining proof is complete;
the item module has zero remaining `sorry`s.

Added one hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeCoefficient_tensorComparison`
(node `lem-sf-native-coefficient-tensor-comparison`, module
`Sheaf.Paper.NativeCoefficientTensorComparison`). Its proof is exactly `by sorry`.
This is a decomposition (one upper hole closed, one lower hole added), not a net
hole reduction. The new statement is only the coefficient derived-tensor step:
it has no Frobenius structure, native Weil objects, or derived-Hom conclusion.
The original Hom comparison still requires the proved adjunction-transport and
composition argument in the item module. No hole occurs in a definition or in
the private helper.

## No longer needed

No existing import was removed and no module is withdrawn or globally pruned.
No direct appeal to `lem-sf-locally-finite-coefficient-ring-realization` or
`lem-pc-sites-sheaf-tensor-bilinear-universal` remains in the item's proof;
these dependencies now belong to the smaller coefficient-tensor lemma. They
remain needed below it and must not be pruned globally. The coefficient module
comparison's constructibility theorem is not used: only its concrete coefficient
isomorphism and the proven scalar-forgetting equivalence are needed. The original
public import remains, because it defines `nativeGeometricForget`.

The proof does not use or import `Sheaf.Paper.NativeGeometricTensorComparison`.
That theorem compares tensors after forgetting Frobenius, whose derived functor
is not an equivalence, and therefore would not by itself justify transporting
internal Hom. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG correctly describes coefficient transport, but its cited interfaces do
not yet state the comparison between the ordinary normalized derived tensor and
the condensed-module derived tensor. A module-category equivalence alone does
not supply this comparison. The new node states precisely this missing tensor
step. Its input is the existing `NativeOrdinaryTensorModels`, so no arbitrary
closed tensor is silently identified with the relative tensor.

The right/left tensor conventions need care: `ordinaryTensorBifunctor` fixes the
right factor, while `CondensedRing.derivedTensor.obj` fixes the left factor. The
new comparison includes the condensed Koszul symmetry. The Hom transport then
uses exactly `C.ordinaryClosed.adjunction P` and the existing condensed unary
adjunction, with no assumption that an arbitrary constructible object is perfect.

Read the latest blueprint internal-Hom paragraph and the current general
biduality unit; the latter's realized statement and steps lists are empty, and
the proof keeps the original closed-forgetful and relative closed-Hom route.
No rework row or current return for this item was found.

## New nodes

`lem-sf-native-coefficient-tensor-comparison` is the coefficient-tensor part of
steps 2--3 of the item's existing plan. It quantifies over an ordinary product-Hom
model and a closed tensor with the existing K-flat total-tensor normalization.
It asserts only a natural isomorphism of fixed-factor tensor functors under the
concrete coefficient equivalence. Its docstring and node give the balanced-map,
total-complex, K-flatness, localization and symmetry argument. The edge cases
are zero factors, the empty scheme and unbounded complexes; none requires a
finite-rank or constructibility condition. Source and three actual search kinds
are recorded. Blueprint search found no duplicate and ancestor lookup returned
null, as for the parent. No change record is needed because existing interfaces
are unchanged.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
