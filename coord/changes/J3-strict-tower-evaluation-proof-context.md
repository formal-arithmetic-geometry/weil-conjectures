# AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_evaluation

## Reason

Prove the existing evaluation identity by comparing the two normalized module
compositors, lifting their equality to strict towers and derived categories, and
combining the existing proper/open evaluation calculations. Generic private
categorical lemmas keep the proof from repeatedly expanding scheme-indexed
module functors. A direct expanded proof checked but exceeded the file time limit.

The new proof-local section, namespace opens and local irreducibility attributes
are recorded because they change elaboration commands. They do not change any
public declaration signature, definition, instance or public import. No other
module is adapted. No target statement or target meaning changes.

## Old

The existing theorem's proof was `:= by sorry`. The module had no `Evaluation`
section, no private `cbcEvaluation*` helper declarations, and no proof imports
of `RelativeCompactSupportPasting` or `StrictTowerProperOpenArrows`.

## New

The same theorem has a complete proof, with no added hypotheses and no new holes.
All added helper declarations are private proved theorems. The proof imports are:

```lean
import all Sheaf.Paper.RelativeCompactSupportPasting
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
```

The new scope commands, closed by `end Evaluation`, are:

```lean
section Evaluation
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] proEtaleRingModuleAdjunctionNormalized
  proEtaleRingModuleUnitSection proEtaleRingCompositeCoefficients
  proEtaleRingDerivedPullbackFactors CochainComplex.IsAcyclicTensorKFlat
  SheafOfModules.IsFlatOnSite proEtaleRingDirectImageMap
```

The section also declares `variable (B : Type (t + 1)) [CommRing B]` for the
private comparison lemmas. The public theorem continues to use its original
coefficient variable `A`; its signature is unchanged. The local linter options
avoid replay of proof tactics on large categorical terms. No diagnostic profiler
or trace option remains. The existing ringed and constant-coefficient definitions
are preserved verbatim.

## Users

`tools/downstream.py Sheaf.Paper.CompleteProetaleStrictTowerRealization --uses
completeProetaleStrictTowerRealization_evaluation` lists the following transitive
consumers. Their statements and definitions retain exactly the same meaning; no
consumer adaptation is needed. The delivery changes no exposed import or instance.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.FourierTransform.FourierDeligneTransform` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicCompletedProjectionShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicExceptionalShiftCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityCanonicalSourceCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicTraceTensorShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceLastFactorProduct` | H2 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceProductDomain` | R8 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceContractionProduct` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceProductData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceSuccessorContraction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationIdentification` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompactificationOpenLimit` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompactificationPushLimit` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompactificationScalarData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompleteCompactificationLimitRealization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompleteCompactificationLimitSupport` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompletedOpenExchangeLimitNormalization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompletedOpenFiniteTransposeCoherence` | M2 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompletedOpenScalarLimitSquare` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompletedOpenStrictMateIdentification` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompletedOpenStrictMateTranspose` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationEigenvalues` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionReconstruction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionSourceComparison` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralCompositorLimitRealization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralOrientationShiftedSheafModels` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisonData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | H5 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralSmoothAdjunctionPresentation` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralTowerImageReconstruction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralTowerProjectionMates` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent` | P9 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | X3 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilPairingCoordinates` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilTensorRepresentatives` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilTransportUnitShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | V5 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralCompletedCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralGeometricInputNormalization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralStrictCalculus` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralStrictReduction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralTotalUnitEquation` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurStrictIntegralExchangeData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurStrictIntegralExchangeNormalization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RelativeKunnethCubeFactorTransport` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeReindexing` | U2 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeReindexingData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfNormalizedCommonStageWeilSquares` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfNormalizedRationalClosedComparison` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfNormalizedRationalWeilSquares` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SfRecollementReductionBoundary` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientModels` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationDescentSpecification` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationIdentificationSpecification` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.StrictReductionCompactSupportNormalization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | P3 | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TensorMapPresentationIndependent` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TensorMateInvertibleInput` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicIdentification` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCoefficientCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarPrimitives` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VerdierHomChainComposition` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenExchangeConstruction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenTransposeNaturality` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilPullbackFibreReturn` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlCanonicalImmersionCohomology` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlImmersionPullbackWeightPreservation` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlOpenDiagramComparisonTransport` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlWeilHeartLocalizationExact` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.Paper.ZlWeilShriekCoefficientLongExact` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | W4 | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompactifiedProperTowerExchange` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedOpenCartesianIdentity` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedTensorSlotShiftLaws` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstruction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.FiniteOpenCartesianCalculus` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | X6 | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquare` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquareData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCoefficient` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCompletion` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateDescent` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateFinite` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateIntegral` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenExchangeRoosRestriction` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorExchangeRealization` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenSupportStepBounds` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.StrictCompactificationProjectionShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.SupportedWeilMateLift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemTensorShiftCoherence` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels` | unclaimed | Same statements and definitions; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same statements and definitions; no adaptation. |

## Status

landed 20261025T210748-L-3584968 2026-10-25 (merge of deliver/J3/Sheaf.Paper.CompleteProetaleStrictTowerRealization)
