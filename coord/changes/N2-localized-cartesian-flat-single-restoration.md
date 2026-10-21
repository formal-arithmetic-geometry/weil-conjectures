# AlgebraicGeometry.localized_cartesian_flat_single_comparison

## Reason

Repair the return of head 9e329642cde. StandardFlatSingleBaseChange was removed
after the returned delivery's base; restore its full quarantine source rather
than treating it as an adaptation of a live file. The server has since restored
that dependency with public adopted-source imports. A server claim request was
refused because it now has no sorry on main. Preserve those current imports in
the packet. Restore the localized item from quarantine and redirect its private
proof import away from a retired empty wrapper to the adopted source module.
All theorem signatures, bodies, docstrings and DAG attachments remain unchanged.

## Old

The quarantined dependency has:

```lean
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
```

The quarantined localized item has:

```lean
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

Both original paths were absent in the shared snapshot of the returned head.

## New

Restore the dependency with the public imports now present on the server main
branch, preserving the concurrent restoration verbatim:

```lean
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
```

Restore the localized item with the private proof import:

```lean
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

Every other byte agrees with the quarantine source. The dependency also agrees
byte-for-byte with the current server source. There is no definition or statement
change, hence no change of target meaning. Existing node fields, Lean attachments
and proof dependencies remain intact.

## Users

The downstream.py check cannot resolve the standard comparison while its source
is absent in the shared snapshot. The manual import-closure check covers 74 modules
across both live sources and quarantine. Searching imports and declaration
uses in both lean/ and quarantine/ finds the restored module as the sole direct
caller and the following transitive consumers. The archived direct caller of the
restored theorem, CartesianFlatSingleLocalizedBaseChange, compiles unchanged in a
scratch consumer check against both delivered modules. It is not included in the
delivery. There is no definition or public signature whose meaning changes, and
no consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | N2 | Restore the archive and redirect its proof import; same theorem and proof. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed in shared snapshot | Restore from quarantine; preserve the current server public imports and unchanged theorem proof. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed in shared snapshot | Transitive consumer, including archives; identical declaration types and meanings; no adaptation. |

The server compilation of both delivered modules passed with no warnings:
StandardFlatSingleBaseChange in 4.0 s and LocalizedCartesianFlatSingleComparison in
15.9 s. The unchanged archived consumer compiled in 10.7 s in the same module set
against the final packet. Its scratch source is excluded from delivery. Import-direction checks
permit both replacements, with no cycle. The independent delivery review and the
maintainer's global build remain the project acceptance checks.

## Status

landed 20261021T193702-L-1264639 2026-10-21 (merge of deliver/N2/Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison)
