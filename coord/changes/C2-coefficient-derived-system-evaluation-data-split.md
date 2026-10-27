# C2: split coefficient evaluation interfaces from their existence proof

## Reason

The assigned existence theorem needs independent normalized-resolution and projection
lemmas. Those lemmas use its structures, so leaving the structures in the existence
module would introduce an import cycle. Extract the original interface and its proved
representative calculations into a publicly re-exported data module.

## Old

Sheaf.Paper.CoefDerivedSystemEvaluationCalculus declared the fiber/calculus/coherence
structures, concrete coefficient comparisons and proved representative calculations,
followed by one unproved existence theorem. The 65 declarations before that theorem
(including one private helper) are the unchanged source prefix.

## New

Those 65 declarations, including their signatures, attributes and bodies, are verbatim in Sheaf.Paper.CoefficientDerivedSystemEvaluationData. The original module retains
every original public import and publicly imports the data module, so all original
names, instances, attributes and definitions remain available with identical types
and bodies. No declaration is withdrawn or renamed. Two proved public generic lemmas
are added: coefficientClosedEnriched_isIso and coefficientClosedEnriched_naturality.
A new propositional structure CoefficientDerivedSystemProjectionModels records the ordinary
sections/limit projection and the finite scalar Hom-zero normalization. It chooses no data.
Elaboration is synchronous in the extracted file; all original declaration bodies remain
identical. The original existence theorem is assembled from two strict subclaims and elementary
categorical proofs. No statement, universe, target or definition is weakened.

The lean owners of def-coef-derived-system-calculus-data and
def-pur-coefficient-reduction-presentation move to the data module. Their node
statements are unchanged. The existence node records the new proof route.
No existing module other than the assigned item is changed.

## Users

The table conservatively includes each direct importer and every transitive importer
with a textual mention of a moved name. All retain the same re-exported interface.
All 59 current direct importers were checked individually against the sandbox: 57
pass within 60 seconds. FlatScalarEvaluationModel and DerivedAutomorphismHomEvaluation
exceed 60 seconds by the same amount against the original item; the report records
both baseline comparisons for independent review. No consumer adaptation is delivered.

| Module | Effect |
| --- | --- |
| Sheaf.Algebra.Homology.FlatScalarEvaluationModel | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Algebra.Homology.ScalarHomComparisonTower | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Algebra.Homology.ScalarHomDerivedSquareCoherence | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.AugmentedReductionNaturality | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CanonicalOpenRestrictionModel | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefNativeOpenTensorGammaEvaluation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefNativeOpenTensorModelsDataExistence | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefNativeOpenTensorModelsExistence | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefOpenTensorEvaluationData | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CoefficientEnrichedGlobalShift | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefficientExtensionOrdinaryQuotientIso | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CoefficientExtensionReductionData | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CoefficientExtensionReductionModel | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CoefficientExtensionRepresentativeRoos | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefficientExtensionStrictDerivedComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefficientExtensionStrictRepresentatives | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefficientExtensionStrictTensorNormalized | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoefficientReductionNaturalCochainComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoherentPrimitiveReductionPresentation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoherentQuotientModelComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CoherentQuotientReductionComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CommonTensorComparisonConstruction | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CommonTensorComparisonDescent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CommonTensorComparisonRepresentatives | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompactSupportCoefficientTransition | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CompactSupportInputTowerCompatibility | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompactSupportNativeSystemEvaluation | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CompactSupportReductionTower | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedComparisonQuotientNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedComparisonQuotientRealizationDefs | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedHomScalarTranspose | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedOpenTensorRepresentativeData | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedOpenTensorRepresentatives | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedOpenTensorSystemRealization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CompletedPullbackTensorComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedPullbackTensorEvaluationCube | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CompletedPullbackTensorProofImplementations | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedPullbackTensorPullbackCounit | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedPullbackTensorTensorCounit | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedPullbackTowerCore | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedPullbackTowerRealizations | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedQuotientReductionPresentation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedUnitPullbackData | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletedUnitStrictComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletionUnitCanonicalModels | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletionUnitDerivedAdjunctionComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletionUnitFiniteMateComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletionUnitFixedCalculusModels | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CompletionUnitModels | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.CompletionUnitStrictQuotientModel | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.CondensedCompactSupportProjection | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.DerivedPullbackTensorHom | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.DerivedPullbackTensorIso | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.DirectImageChangeRingTranspose | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.EffectiveCompletionPresentationModels | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.EffectiveQuotientModelDescent | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.ExplicitScalarConeWordCoordinates | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.ExpressionCounitSubstitutionCoherence | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FdCompletedCompositorNormalization | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.FdPullbackAugmentationCounitMatching | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FdScalarPullbackRealizationIdentification | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteCounitRestrictionTowers | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.FiniteEtaleDiagonalCoordinates | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteExpressionReductionComparison | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.FiniteFreeScalarDerivedComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteOpenGammaRestriction | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteOpenProductOperations | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteOpenProductRestriction | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteOpenProductSwap | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FinitePullbackTensorQuotientRepresentatives | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteQuotientPullbackDescent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteRationalDerivedOperations | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.FiniteRestrictionCoefficientCore | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteRestrictionConstructibleVertices | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteRingSectionDeformation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteSmoothDeformationNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteSmoothDiagonalNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteSmoothGammaConstructions | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteSmoothOmegaTensorCoordinates | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FiniteSmoothTensorNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralCoefficientRoosCoordinates | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralCoherenceData | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralComparisonCanonicalShifts | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralComparisonPullbackRealizationShifts | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralComparisonRealizationModels | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralComparisonScalarRealizationShifts | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralComparisonSystemData | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralCompositionCounitImages | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralFiniteScalarModelDefinitions | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralFiniteScalarPerfectModel | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralGoodQuotientPresentation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralImmersionPullbackNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralImmersionPullbackNormalizationData | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralImmersionShiftCompatibility | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralMappingLimitProjections | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralOperationRoosEffectivity | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralOperationsScalarComparisonModels | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralPullbackComposition | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralPullbackCounitProjection | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralPullbackReductionCounit | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralPullbackStrictFiniteComponent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralPullbackSystemComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralScalarTowerEffectivity | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralStratumChartRestrictions | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralStratumChartRestrictionsCharts | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralStratumChartRestrictionsData | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralStratumChartRestrictionsFunctorial | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IntegralStrictReductionModel | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IntegralTowerLimitComparison | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.InternalSectionHomComparisonData | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.InternalSectionScalarHomTransportData | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IsomorphismComparisonNatural | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IsomorphismDerivedPullback | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.IsomorphismPullbackRawStage | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.KummerPartialNerveCoordinates | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.KummerSuccessiveDescent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.LocalFrobeniusTrace | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.MixedReductionUnitComposition | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.NormalizedArithmeticInterpolation | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.NormalizedCompletedOperationModels | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.NormalizedCompletionRealization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.NormalizedTensorConstraintTransport | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.OpenRestrictionAugmentedDescent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.OpenRestrictionCounitOnGoodComplexes | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.OrdinaryCompactSupportCoefficientTransport | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.OrdinaryQuotientPullbackSuccessor | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.OrdinaryQuotientPullbackTowerComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PodCompletionReindexModels | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PodCompletionScalarFormulas | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PodCompletionUnitScalarIntertwining | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PodCounitScalarWordCoordinates | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PodIdentityReductionTower | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PodQuotientAdjunctionRealization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PointAutomorphismDerivedTransportInverse | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PrimitiveCounitComparisonModels | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PrimitiveCounitEvaluation | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PrimitiveCounitPullbackRealization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PrimitiveCounitTensorRealization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PrimitiveQuotientPullbackModelExistence | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PrimitiveQuotientRealizationComparisons | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PrimitiveQuotientRealizationsTransport | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PrimitiveQuotientRealizationsUnique | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PrimitiveQuotientScalarModelExistence | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PurReductionFiniteShiftNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PurReductionLimitShiftData | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PurSequenceAdjointResolutionData | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.PurSequenceAdjointResolutionShifts | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurSequenceComparisonTranspose | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurSequenceDerivedNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurSequenceKFlatComparisonData | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurSequenceKFlatComparisonShifts | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurSequenceProjectionHomNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurSequenceReductionShifts | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.PurSequenceReductionUniversal | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.QcqsCompactSupportNativeTowerComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.QuotientExpressionKFlatNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.QuotientExpressionKFlatOperations | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.QuotientExpressionStrictKFlatTowers | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.RingedRestrictionStrictLimitCoherence | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.RoosAdjunctionQuotientNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.SequenceAdjointShiftInterfaces | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.SequenceKInjectiveComparisonShifts | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.SfAmbientIntegralDirectImage | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.SfFrameworkCommonStageDescent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.SfIntegralDirectImageShiftComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictLineHeartAssembly | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictPullbackAdjointConstructor | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictQuotientExpressions | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictQuotientLevelwiseFlatModels | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictReductionPresentationMap | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.StrictScalarPullbackComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictTensorAdjointConstructor | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictTensorOrdinaryAdjunct | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.StrictUnitOrdinaryAdjoint | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.SupportedHomPullback | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.SystemProperOpenInvertibility | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.SystemScalarTransitionComparison | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.Paper.TensorReductionFiniteComponentEquation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TensorReductionFiniteComponents | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TensorReductionFiniteProjection | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TensorReductionOrdinaryModel | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TensorReductionOrdinaryTranspose | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TensorReductionStrictComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TensorReductionStrictFiniteEquation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TowerOperationsGroundFieldRetagging | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TowerReductionShiftCompatibility | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TransportedReductionPullbackNormalized | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TransportedReductionScalarNormalized | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TransportedReductionSystemsNormalized | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.TwoOpenTensorChainNormalization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Paper.ZlFiniteIntegralFibreReconstruction | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.AugmentedStrictIntegralCompletion | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.IntegralOpenReductionDefinitions | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.SixFunctors.IntegralOpenReductionQuotientSquare | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.IntegralOpenScalarRestrictionComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.IntegralOpenTensorRepresentative | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenDvrAugmentedReductionComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenDvrAugmentedTowerComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenDvrDerivedTowerComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenDvrScalarUnitFormula | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenDvrStrictReductionComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenQuotientKoszulCompleteness | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.SixFunctors.OpenQuotientKoszulModels | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenSemilinearReductionDescent | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OpenSemilinearTensorModelData | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.OrdinaryReductionAugmentedComputation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.ScalarSixLisseTowerComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.SixFunctors.ScalarSixPullback | Unchanged re-exported interface; transitive textual user. |
| Sheaf.Targets.VectorBundlePurity | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.AutomorphismTensorReductionComparison | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.CompactSupportSystemNormalizedPresentation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | Unchanged re-exported interface; direct importer checked separately. |
| Sheaf.TraceFormula.IsomorphismStrictQuotientModels | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.OrdinaryQuotientTowerComparison | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.ScalarModelAssociativity | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.ScalarModelIteratedStrictCalculation | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.ScalarModelRoosZeroLift | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.ScalarModelUnit | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.ScalarPresentationKFlat | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.StrictQuotientCompletionRealization | Unchanged re-exported interface; transitive textual user. |
| Sheaf.TraceFormula.StrictQuotientCompletionUnit | Unchanged re-exported interface; transitive textual user. |

## Status

landed 20261027T180505-L-3866562 2026-10-27 (merge of deliver/C2/Sheaf.Paper.CoefDerivedSystemEvaluationCalculus)
