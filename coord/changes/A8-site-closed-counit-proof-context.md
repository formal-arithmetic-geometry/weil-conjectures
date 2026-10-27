# AlgebraicGeometry.ProEtale.siteClosedCounitTransport proof context

## Reason

The proof compares two existing canonical compact-support comparison constructions.
The bounded-below inclusion is definitionally an inclusion, but unrestricted unfolding
of the exact and right derived functor constructions makes component matching expensive.
The private comparison helper keeps both functors irreducible locally and uses their
explicit naturality and inclusion equations. The maxHeartbeats setting is local to this
helper; the fixed 60-second server limit is unchanged. These commands affect elaboration
only. The supplied ordinary adjunction gives the public theorem without any new assumption.

Both existing public imports, the theorem signature and its docstring are unchanged.
No public definition, instance, attribute or target statement changes. Two proved private
helpers are added. All six removed imports were private proof imports. No consumer
adaptation is needed and no target statement review is reopened.

## Old

There were no local reducibility commands or local maxHeartbeats commands at this theorem.
Its proof was `by sorry`.

## New

Commands scoped to the proved private `compact_comparison_eq` helper:

```lean
set_option maxHeartbeats 600000 in
-- Keep the large comparison composites folded while matching their components.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor in
```

The public theorem's backward elaboration options are confined to its proof body.
The new private import is
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.

## Users

Source import-graph audit: 112 transitive consumers at the audit snapshot, four direct
importers. `tools/downstream.py --uses siteClosedCounitTransport` finds no consumer
currently mentioning the theorem; unfinished parent proofs still require its node.
All retain the same visible interface. No consumer source is edited in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.DualizingClosedSite | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteTorStability | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | claim present | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | claim present | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed in shared claim snapshot | Identical public interface; no adaptation. |

## Status

landed 20261025T100805-L-3623522 2026-10-25 (merge of deliver/A8/Sheaf.AlgebraicGeometry.SiteClosedCounitTransport)
