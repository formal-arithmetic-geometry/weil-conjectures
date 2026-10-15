# Sheaf.CategoryTheory.SiteInverseImageTensor public imports

## Reason

The public tensor statement-module import is unnecessary for either unchanged theorem
signature or proof. Both use the source library's canonical localized sheaf tensor.
Removing this import prunes an unnecessary statement-module dependency. All declaration
signatures, universes, visibility and definitions remain unchanged.

## Old

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
```

## New

The import is removed. No replacement public import is necessary. The remaining public
imports provide the objects, instances and definitions in both original signatures.
New proof-only imports are private; they are listed in report.md.

## Users

All five direct importers use a private import of this module. Each original importer
was compiled individually in import order against the changed module using lcompile.py
--all in a scratch sandbox; all passed. No downstream file is adapted. The table includes
all 46 modules returned by tools/downstream.py with both declaration names in --uses.
The import change does not alter any target's statement or definitions.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | Original compiles against changed module; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleInverseImage | unclaimed | Original compiles against changed module; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOperations | E4 | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.CategoryTheory.RingedToposSitePresentation | unclaimed | Original compiles against changed module; no adaptation. |
| Sheaf.Paper.AdicLisseModule | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | Original compiles against changed module; no adaptation. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.KFlatRingedToposPullback | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.ProEtaleConstructibleSheaf | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | No signature or definition change; no adaptation. |
| Sheaf.Paper.ProfinitePointPullback | B4 | Original compiles against changed module; no adaptation. |
| Sheaf.Paper.RingedPullbackPreservesKFlat | unclaimed | No signature or definition change; no adaptation. |
| TargetsCheck | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No signature or definition change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | No signature or definition change; no adaptation. |

## Status

landed 20261015T154158-L-160393 2026-10-15 (merge of deliver/C4/Sheaf.CategoryTheory.SiteInverseImageTensor)
