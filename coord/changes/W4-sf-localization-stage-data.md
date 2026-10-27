# WeilConjectures.SfSupportedLocalization

## Reason

Separate the existing record definitions from the theorem that uses the new coefficient-passage lemmas. This permits those lemmas to import the record types without an import cycle. This is a data-interface extraction, not a split to evade a compile timeout. Every existing signature and every moved declaration body is unchanged, including the proved exceptional inverse-limit formula. Public imports are retained verbatim in the extracted module and publicly re-exported by the original module. Unused private proof imports are removed. No target meaning changes.

## Old

Original public imports of Sheaf.Paper.SfLocalizationAllStages:

```lean
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement
```

The 21 existing declarations other than the two all-stage theorems were declared in this module.

## New

```lean
public import Sheaf.Paper.SfLocalizationData
```

SfLocalizationData has exactly the old public imports above. It contains the same 21 declarations verbatim, with the same namespaces, signatures, fields, bodies and attributes. The original module retains both theorem signatures and publicly re-exports the data module. The integral exceptional-limit proof is preserved completely. The new three construction lemmas import only the data, preventing a dependency cycle.

## Users

A source-level comparison checked all 23 existing signatures and all 21 relocated bodies. All 116 transitive importers are listed below. The two direct consumers are Sheaf.DeligneLaumon.QbarCurveDuality and Sheaf.Paper.FiniteClosedShriek. Neither needs source adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | B4 | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | D2 | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | B6 | Same public names, signatures and definition bodies through the re-export; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same public names, signatures and definition bodies through the re-export; no adaptation. |

## Status

landed 20261025T101804-L-3736516 2026-10-25 (merge of deliver/W4/Sheaf.Paper.SfLocalizationAllStages)
