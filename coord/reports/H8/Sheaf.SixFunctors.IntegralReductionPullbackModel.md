## What changed

Proved `integralReductionPullbackModel` without changing its statement or the
`RealizationModel` definition. Added the proof-only import
`Sheaf.SixFunctors.IntegralOrdinaryLimitModel` and private proof imports of
`IntegralOperationsWellDefined` and `VaryingRingOperations`. Both are already in
the original import closure; these proof imports introduce no additional existing
modules into that closure.

The completed-direct-image comparison module proves the identity-section
identification of the two completed module direct-image presentations by the
adjunction hom-equivalence. Its uniqueness fixes the comparison used downstream.
The new tower-comparison module constructs the unique normalized tower isomorphism
from the published finite direct-image/evaluation and direct-image/scalar-restriction
isomorphisms. The ordinary-limit module uses that proved unique comparison.
The right adjoint preserves ordinary limits; its projection equation proves the
specified section formula, including the equality transports in the restriction
functor. Its only public declaration is `integralOrdinaryLimitModel`.
The explicit finite construction and the limit calculation are in separate modules
for compilation; the selected tower is determined by the proved uniqueness theorem.

The item uses the proved preservation of flat-term K-flat complexes by ringed
pullback. On the full good-complex subcategory, it conjugates the ordinary
comparison by the published reduction models and exact-pullback factorizations.
Localization descends this natural isomorphism; cancellation proves exactly the
required whole-system representative equation. No finite derived evaluation is
used to detect an equality.

Validation: `lcompile.py --all` passed for all four delivery modules.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralReductionPullbackModel`
(node `lem-sf-integral-reduction-pullback-model`): 1 of 1 original holes.
Added and proved
`WeilConjectures.IntegralSystemRealization.integralCompletedDirectImageComparison`
(node `lem-sf-integral-completed-direct-image-comparison`),
`WeilConjectures.IntegralSystemRealization.integralOrdinaryTowerComparison`
(node `lem-sf-integral-ordinary-tower-comparison`) and
`WeilConjectures.IntegralSystemRealization.integralOrdinaryLimitModel`
(node `lem-sf-integral-ordinary-limit-model`). Zero holes added, zero split-off
unproved statements, and zero holes left in all four delivery modules.
The proof uses existing library declarations; their transitive proof obligations
are not claimed closed by this delivery.

## No longer needed

No original public import is removed and no module is withdrawn.

The item no longer directly needs `lem-pur-flat-roos-functor-descent`
(`Sheaf.CategoryTheory.FlatRoosFunctorDescent`): the desired comparison is an
ordinary adjoint-conjugate comparison descended through the existing localization
of good complexes, without constructing a new Roos realization.

The item does not directly use `lem-pc-kflat-resolution`
(`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`): its required
localization property is already proved in `IntegralOperationsWellDefined`.
K-flat resolutions remain a dependency of that existing localization theorem;
this is not a claim that the resolution module can be removed globally.
All other original declared dependencies are retained. The DAG records the new
ordinary construction and the reused ringed K-flat preservation helper.

## Where the brief, the DAG or earlier work was wrong

The original plan was usable but unnecessarily invoked a fresh flat-Roos descent.
The library already supplies the localization needed to descend the whole-system
comparison directly. The ordinary part also reuses the published normalized finite
coefficient square instead of reconstructing scalar restriction.

The new ordinary construction is categorical and includes identity morphisms,
zero modules, empty schemes and arbitrary systems; it imposes no completeness,
boundedness, finite Tor-amplitude or invertibility hypothesis on the input system.
The unit route and all original declaration signatures remain unchanged.

## New nodes

`lem-sf-integral-ordinary-limit-model` records the proved ordinary-limit portion of
primitive realization Step 3. Its theorem is strictly the ordinary comparison and
projection formula, with no derived reduction or K-flat representative clause.
`lem-sf-integral-completed-direct-image-comparison` records the proved identity-section
comparison of the two completed direct-image functors and its uniqueness.
`lem-sf-integral-ordinary-tower-comparison` records the proved finite tower
construction and its uniqueness by component sections.
No change record is required: only the item, its node and new modules/nodes
are changed, and no existing interface or definition is altered.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
