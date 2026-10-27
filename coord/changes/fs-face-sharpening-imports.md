# AlgebraicGeometry.face_sharpening imports

## Reason

The complete proof constructs localization units directly and proves torsion-freeness
from sharpness and saturation. It no longer uses the two Sheaf dependency theorems.
Drop their public imports. Retain the public Mathlib quotient definitions needed by
the statement and the saturation predicate used by the proof and existing consumers.
No declaration signature, visibility, attribute or definition changes. No target
statement or definition changes meaning.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FaceLocalizationUnits
public import Sheaf.AlgebraicGeometry.FaceSubgroupSaturated
```

## New

```lean
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Saturated
```

The proof additionally privately imports
`Mathlib.GroupTheory.MonoidLocalization.Finite` for finite generation of completions.
All added helpers are private and proved.

## Users

A source search finds no uses of either removed theorem outside its defining module.
`tools/downstream.py Sheaf.TraceFormula.FsFaceSharpening --uses face_sharpening`
finds 165 downstream modules and no textual theorem users outside the item.
The table records their current holders from the shared snapshot. The 36 direct
importers were compiled from unchanged copies against the changed item: all passed,
with a maximum of 15 seconds per consumer. These verification copies were removed
from the packet afterward; no adaptation was necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianInertRigidificationCover | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.AffineFanGermRigidity | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.AffineFanHomUniversal | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.AffineFanLocalizationSections | P1 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal | V2 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.BlowupLocalDimensionBound | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.CharacteristicZeroLogResolutionIndependence | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.CodimensionResolutionImprovement | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.CodimensionResolutionPrefix | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.CompleteLocalRigidificationComparison | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.ConductorNormalizedResolutionExtension | T2 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.CospanCompatibleFSCharts | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.EquivariantLogSmoothFanRegularization | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FSLogInfinitesimalCriterion | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.FSLogSmoothCompositionStrictBaseChange | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FanCenterLocalBlowupCharts | F7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FanChartLocalMonoidLift | F8 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.FieldLogSmoothGabberModification | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FineFanBlowup | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.FineFanPointLocalization | G5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FormalChartGeometricRegularity | R7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary | R9 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FunctorialFanDesingularization | V3 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.FunctorialLogBlowupEtaleDescent | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbelianStageToricChart | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsoluteEquivariantModification | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.GabberLogBlowupRegularization | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.GabberModificationData | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.InducedNormalizedLogResolution | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.InertEigenparameterRigidificationData | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.IntegralMonoschemeRealization | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.IntegralToricTowerProper | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.KatoLatticeChartRealization | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.KummerBoundaryRestriction | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.KummerFixedSharpChart | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.KummerGCover | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.KummerGCoverFSBaseChange | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.KummerSaturatedPushoutAlgebra | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.KummerStrictLocalStandardModel | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LatticeTorusCoordinatesAction | B8 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LocalBlowupTowerGlobalization | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogBlowupFullPullback | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogBlowupNormalization | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogCharacteristicIdeal | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogCotangentCharacteristicQuotient | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogFanChartBlowup | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.LogMonoidalAssociatedPoints | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.LogRegularCompletedChart | U6 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogRegularGenerization | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogRegularMonomialTensor | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.LogRegularPairRegularPullback | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogRegularSharpChart | U7 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.LogSmoothDifferentialGenerators | U8 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogSmoothLogRegular | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.LogSmoothPreservesLogRegularity | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.LogTowerCenterDescentDatum | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogTowerContractionDescent | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogTowerCoverRigidity | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.LogTowerEffectiveCenterDescent | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFan | H9 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood | E5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoidPrincipalOpenFace | B9 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoidSpectrumHomUniversal | D6 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoidalChartDenseInjective | E7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonomialReesChartComparison | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoschemeFiniteChartComponents | F5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoschemeSmoothLocalCharts | C5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoschemeToricRealization | F6 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoschemeToricTowerDescent | J5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.MonoschemeTowerComparisonCoherence | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianLogPairStrictResolution | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedBlowupTowerEtaleDescent | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedOrdinaryResolution | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedTowerDescentData | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedTowerRecoveryTests | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedTowerRegularPullback | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.NormalizedTowerSupportRecovery | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.PointwiseLogRegularCompletion | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.PolynomialLogChartRegularity | J9 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.PrelogChartFsUniversal | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.PrimitiveMonomialTraitGeometry | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveFiniteGroupQuotient | F9 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLogRegularResolution | G5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.QEConductorNormalizedResolutionExtension | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.QENormalizedResolutionRule | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.QEOrdinaryRegularResolution | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.QuasiSplitTowerSmoothResolution | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.RationalToricCompletionRegularMap | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart | G7 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.RegularNormalizedResolutionRule | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.RigidifiedQuotientTowerComparison | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.SaturatedLogBlowupChartCover | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.SharpSectionBasicChartData | G7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.SharpeningBlowupChartComparison | G9 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.SimultaneousCohenRigidificationLift | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.SmoothFunctorialNormalizedToricDesingularization | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.SmoothMarkedLogChart | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.SmoothNormalizedResolutionRule | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.SmoothToricSaturatedSharpReduction | D7 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.SplitLatticeTorusProjection | E8 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison | D8 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.StrictLogBlowupCartesian | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.TameTraitQuotientLogEtale | G9 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.ToricMonoidComparison | M7 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.ToricRealizationFiniteType | M8 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.TraitPrimeToEllLogAlteration | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.VeryTameEquivariantSharpChart | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.AlgebraicGeometry.VeryTameLogQuotient | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.VeryTameQuotientLogRegular | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.AlgebraicGeometry.ZariskiFsMonoidChart | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.DeligneLaumon.TraitLogSmoothUniformizerChart | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.GroupTheory.FineMonoidUnitGenerators | T7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.GroupTheory.FineMonoidUnitSplitting | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.GroupTheory.IntegralSharpeningGroupExactness | J6 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.AffineMonoidAlgebraNormalization | R7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.AffineToricEquivariantIdeals | V7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CohenMonoidSubstitutionParameter | V5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CohenMonoidSurjectionPrincipalKernel | T7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CompleteModelFaceQuotients | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CompleteToricFaceStrata | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.RingTheory.CompleteToricFacetValuations | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CompleteToricLocalizedUnitDivisorLift | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CompleteToricModel | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CompletedChartCoefficientSurjection | U5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.CompletedInvertibleKummerMonoidExtension | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.RingTheory.CompletedMonomialTransverseParameter | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.RingTheory.CompletedTameMonoidBaseChangeModel | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.RingTheory.FacetLatticeSupportedCoordinateCover | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.FilteredMonoidCoefficientLimit | X5 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.FormalMonoidExtensionModel | V7 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.RingTheory.FormalMonoidRingDimension | W7 | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.RingTheory.IntegralSupportSaturation | Z8 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.IntegralSupportWeightedInitialDegree | S7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.MonoidAlgebraDomainFraction | Z9 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.MonoidFaceLocalizationIdealTensor | C8 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.MonomialIntegrality | Y6 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.PolynomialMonoidLiftStratum | Z7 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.PositiveMonoidAdicFiltration | P3 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.SaturatedMonoidAlgebraNormal | U4 | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.SharpConePrimitiveFacetPreparation | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.RingTheory.SupportedCoordinateCoverUnitsPrimes | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.AffineLiftTowerDescent | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.ChartFaceResidualUnitDecomposition | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.TraceFormula.CompleteToricKatoRecognition | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.CompleteToricMonomialFactors | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.FanDescentRefinementPullback | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.KatoTorIndependenceChart | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.LogChartFaceTorComparison | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.TraceFormula.LogChartStrictLocalTor | unclaimed | Direct importer; verify unchanged source against reduced imports. |
| Sheaf.TraceFormula.LogRegularDesingularization | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.LogRegularDivisorialStructure | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.LogRegularToricRefinement | unclaimed | Indirect importer; declarations and target meanings unchanged. |
| Sheaf.TraceFormula.SharpeningFanBijection | unclaimed | Direct importer; verify unchanged source against reduced imports. |

## Status

landed 20261026T082644-L-2202692 2026-10-26 (merge of deliver/P3/Sheaf.TraceFormula.FsFaceSharpening)
