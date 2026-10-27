# AlgebraicGeometry.Etale.ordinaryFiniteAdjunction

## Reason

Repair C-240da preserves the published OrdinaryFiniteP1Arrows and
OrdinarySupportedKummerSystem files byte for byte, including their elaboration
contexts, definition bodies and generated auxiliary constants. The returned
packet changed those bodies and broke unfolding consumers; that change is
withdrawn. The new OrdinaryFiniteCoefficientRecords module contains the
canonical finite adjunction record, normalized
arrow pullback, direct-image additivity, and proved equations relating the
published projective-line components to the recorded adjunction.
OrdinaryFiniteConstantUnitComp contains the proved equations and composition
law for the unchanged supported unit. None of those published arrow or supported-unit
definitions is replaced by a record or wrapper. FiniteP1DiagonalAlpha and SupportedDerivedUnitForget also
return to their exact published versions and require no adaptation.

## Old

The published pullback and pushforward are the original leftDerivedFunctor and
rightDerivedFunctor; the two projective-line components use the original
canonical derived adjunction, and supportedDerivedUnit uses derivedSingleUnit.
These published definitions, signatures and auxiliary constants are unchanged.

## New

The same published definitions remain verbatim. The new module records their
canonical finite adjunction directly, with an irreducible interface. The proved
ordinaryFiniteP1Unit_eq and ordinaryFiniteP1ChernPushforward_eq equations expand
only that new record and identify its components with the published maps.
The supportedDerivedUnit_eq equation uses the existing proved
ordinaryFiniteUnitPullback_hom interface and derivedSingleUnit_eq; its composition
law specializes the generic constant-unit pasting theorem. These equality
interfaces add no mathematical datum or hypothesis. Unused general coefficient
wrappers and the costly cached-functor conversion theorem from the intermediate
repair are omitted. No published definition or its auxiliary constants are changed.
The unit proof keeps the adjunction record irreducible locally and checks
declarations synchronously; this avoids the first submission's 61-second compile.
The revised proof passes in receipt 32e219e187249a8609de933b.

## Users

The following conservative validation set includes direct importers, declaration
users (including unfolding users), and the six restored original modules.
The published arrow and supported-unit consumers remain unchanged. The separate
ProjectiveLineDiagonalIntegrals proof simplification is recorded in its own change record. The final
compile results and any baseline limitations are documented in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineTraceConstruction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AffineTraceUnitCompactBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationConstruction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.BundleSectionComparisonIsoPasting | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.BundleSectionOrientationMapExt | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.BundleSectionProjectionUnit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.BundleSectionPurityUnitIsIso | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.BundleSectionPurityUnitNormalization | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.BundleSectionRankZeroAffineNormalization | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierEtaleKummerDerivedUnit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierProIntegralResidueDerivedUnit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierProIntegralScalar | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierProKummerDerivedUnit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierReductionData | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierReductionModulus | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ChartSumAffineCounitTransport | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ComparisonConstantGenerator | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCup | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.EtaleDegreeZeroHomRestriction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.EtaleSingleRestrictionComp | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1ChernMapBaseChange | X7 | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback | A2 | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.GabberRegularPairPurity | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.GeoCartierCanonicalChern | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.GeoCartierCanonicalEtale | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClassDefs | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.GeoCartierSourceComparison | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.NormalizedKummerCohomologyArrows | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrderedTateSectionPullback | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassInjectivity | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit | Z8 | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OriginComparisonArrows | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.OriginProjectiveNormalization | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.RegularSupportedClassOperations | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.RelativeKummerStrictLocalInvariance | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.ResidueFiniteRootMapIso | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1ChartExchange | E2 | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison | U3 | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1IntegralTraceComparison | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransport | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransportData | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransport | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse | Q4 | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue | R1 | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SpP1RationalPointChern | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedDerivedUnitForget | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedIntegralResidueSequence | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryPullback | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryScalar | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerChernRealization | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerLocalizationBoundary | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarDerived | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarMaps | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationCartesianPrefix | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationChartCoefficientZero | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationDirectSumLocal | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationIdentityUnit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationOverlapChartPrefix | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationRankZeroLocal | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationRestrictedChartCoefficient | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationRestrictedChartTransport | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationSwapChartPrefix | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationSwapLocal | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit | unclaimed | original source; compatibility validation |
| Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineCoefficientCounitNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineCounitScalar | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineDiagonalPowerCoefficient | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineDiagonalRawTransposePower | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineDiagonalTransposePower | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineOrderedIntegrationData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | original source; compatibility validation |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CartierDualKummerNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ChartGeometricCounitEvaluation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ChernFlagFormula | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CoordinateCounitArrows | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CoordinateLineCounitTensor | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | original source; compatibility validation |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalAffineTraceSiteData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalCounitComparisonData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalExchangeNaturality | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrdinaryChartLift | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrdinaryOrientationRigidity | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrientationChartExistence | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrientationCompatibility | unclaimed | original source; compatibility validation |
| Sheaf.Paper.DiagonalOrientationRefinementData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FieldOrientationSystemComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FramedAbelianRealization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FramedForgetSupport | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FramedScalarMaps | unclaimed | original source; compatibility validation |
| Sheaf.Paper.FramedTransport | unclaimed | original source; compatibility validation |
| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed | original source; compatibility validation |
| Sheaf.Paper.KummerAdditivity | unclaimed | original source; compatibility validation |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | original source; compatibility validation |
| Sheaf.Paper.LocalizedTopChern | unclaimed | original source; compatibility validation |
| Sheaf.Paper.NormalizedCartierForget | unclaimed | original source; compatibility validation |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | original source; compatibility validation |
| Sheaf.Paper.OrderedAffineTraceNormalForm | unclaimed | original source; compatibility validation |
| Sheaf.Paper.OrderedAffineTransposeData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.OrderedIntegrationComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1CounitScalar | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1KummerChernScalar | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1KummerDerivedScalar | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1KummerScalarEndpointComposition | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1KummerScalarEndpointExistence | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1KummerScalarEndpoints | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1KummerTraceSiteTransport | unclaimed | original source; compatibility validation |
| Sheaf.Paper.P1SplittingScalar | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ProjectionUnitIntegration | unclaimed | original source; compatibility validation |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityChernClasses | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityCompositionComparisons | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityDiagonalDualizingData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityFrameKummer | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityOrientationDatum | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | original source; compatibility validation |
| Sheaf.Paper.RamifiedCartierSupportedPurity | unclaimed | original source; compatibility validation |
| Sheaf.Paper.RamifiedRootLimitTorsionUnit | unclaimed | original source; compatibility validation |
| Sheaf.Paper.RankOneKummerGenerator | unclaimed | original source; compatibility validation |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | original source; compatibility validation |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.RelativeKummerCoefficientNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SectionCoordinateCounitNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SmoothPurityMap | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SmoothTrace | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SupportedProjectiveChernComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.SupportedRootScalarSiteComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerOrientationEvaluation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerP1EtaleDelta | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerP1EtaleOperations | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | original source; compatibility validation |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed | original source; compatibility validation |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.UniversalTranslationMultiplier | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | original source; compatibility validation |
| Sheaf.Paper.VectorZeroSectionIntegrationBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.TransportAffineNormalization | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.TransportAffineTrace | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.TransportFiniteLineDerived | unclaimed | original source; compatibility validation |
| Sheaf.SecSmoothPurity.TransportFiniteLines | unclaimed | original source; compatibility validation |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed | original source; compatibility validation |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | original source; compatibility validation |
| Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange | C3 | original source; compatibility validation |
| Sheaf.SixFunctors.ProjectiveLineTraceAdjunction | D3 | original source; compatibility validation |
| Sheaf.SixFunctors.ProjectiveLineTraceCounitBaseChange | unclaimed | original source; compatibility validation |
| Sheaf.SixFunctors.ProjectiveLineTraceModel | unclaimed | original source; compatibility validation |
| Sheaf.SixFunctors.ProperOrderedProjectionExchange | unclaimed | original source; compatibility validation |
| Sheaf.Targets.VectorBundlePurity | unclaimed | original source; compatibility validation |

## Final compatibility checks

The unchanged sources were checked against the fresh delivery artifacts.
All ten direct importers of changed existing modules are included. No consumer
is adapted or withdrawn. Receipts are lcompile result identifiers.

| Module | Result | Receipt |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | passed | bbe253a504ea6bcc00577588 |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | passed | 11052f0bcaf11119cd344b96 |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | passed | 11052f0bcaf11119cd344b96 |
| Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange | passed | 793262267f470597c5d87c27 |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | passed | daf815f1b57c7cb988e591f8 |
| Sheaf.AlgebraicGeometry.FiniteP1ChernAdjunctMate | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | passed | 37f6388554407f12d8fc6db8 |
| Sheaf.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Untwist | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents | passed | 39fea38aa48848e35cd124b9 |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation | passed | 90cbfe5783545488158a5789 |
| Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison | passed | f3880194652c01b322dfb949 |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransport | passed | 4339371c6629a31fe0d75e2b |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransportData | passed | 4ea8c851e75507ba9c075820 |
| Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore | passed | 9496be273a6ea353f5cc9a7a |
| Sheaf.AlgebraicGeometry.VectorIntegrationCartesianPrefix | passed | c43056615f1442883fcc5ecd |
| Sheaf.AlgebraicGeometry.VectorIntegrationRankZeroLocal | passed | 64c5a847fcdef76799d53537 |
| Sheaf.Paper.AffineDiagonalTraceRestriction | passed | 79d6beaeea9b504089f99668 |
| Sheaf.Paper.AffineDiagonalTransposePower | passed | 723c3080e6d29d9ab1387471 |
| Sheaf.Paper.CoordinateLineCounitTensor | passed | 6ba84961badbe99a40244f89 |
| Sheaf.Paper.DiagonalExchangeNaturality | passed | 6418bac775db890db0a523cb |
| Sheaf.Paper.DiagonalOrientationCompatibility | passed | 609fe0bb6fbdf78cd6bb2769 |
| Sheaf.Paper.P1KummerTraceSiteTransport | passed | 76236b318ef1d919af8c2f79 |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | passed | b79232f241813e03a30aea2c |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | passed | 56fc936be04dc1bfdf41b533 |
| Sheaf.Paper.TowerP1KernelScalarData | passed | ad3c09381f7de01c85711720 |
| Sheaf.Paper.VectorIntegrationSiteComparison | passed | 530702ab3508955fb5fa1e1a |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | baseline timeout | b025c63a53cfeaffc23e5356 |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | baseline timeout | 128e4ec2eed9effea9140127 |

GeoP1Cohomology exceeds the limit both without F1
(bf3b2de5c04c4cef31c4201f) and with the final overlay
(b025c63a53cfeaffc23e5356). Its import closure contains no changed F1 module.
The quarantined AlgebraicGeometry.ProEtaleProjectiveLineTrace takes 83 seconds
both without F1 (a8a7be6c6232d2d679bcd6e8) and with the final overlay
(128e4ec2eed9effea9140127). The two sources are unchanged and neither is
adapted or withdrawn. All other listed consumers pass. The paper module
ProEtaleProjectiveLineTrace is a different module and passes.

## Status

landed 20261026T222636-L-676965 2026-10-26 (merge of deliver/F1/Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula)
