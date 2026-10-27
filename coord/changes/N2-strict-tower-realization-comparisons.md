# Strict-tower realization comparison module extraction

## Reason

The declared dependency CompletedOpenStrictMateIdentification imported the item
for its already constructed endpoint comparisons. Importing that dependency from
the item therefore formed a cycle. Move all already proved declarations and all
constructions into StrictTowerRealizationComparisons, preserving every existing
signature and construction body verbatim. The item publicly
reexports the foundation, so existing users keep the same declaration names,
signatures, attributes, data, and public import closure. Both existing holes stay
in the item and receive proofs. This is a dependency repair, not a split to avoid
the compile-time limit. No source-library file or target statement changes.

Five unclaimed Sheaf consumers in the path back to the item need only the
foundation. Redirect precisely those imports. They use no main realization or
ordered open-factor theorem. CompletedOpenStrictMateIdentification and
ConstantTowerSquareNormalization also gain local irreducibility attributes for
standard derived-category and functor records; their existing declaration
bodies remain unchanged. The existing ConstantTowerSquareNormalization
private-helper access is preserved with import all of the foundation.

## Old

The item directly declared the comparison definitions, the proved auxiliary
lemmas, and the two holed realization theorems. In each of the four open modules:

```lean
public import Sheaf.Paper.CompleteProetaleStrictTowerRealization
```

In ConstantTowerSquareNormalization:

```lean
import all Sheaf.Paper.CompleteProetaleStrictTowerRealization
```

## New

The item publicly imports the unchanged constructions and proved auxiliaries:

```lean
public import Sheaf.Paper.StrictTowerRealizationComparisons
```

The four open modules now use:

```lean
public import Sheaf.Paper.StrictTowerRealizationComparisons
```

ConstantTowerSquareNormalization now uses:

```lean
import all Sheaf.Paper.StrictTowerRealizationComparisons
```

All moved declaration signatures and non-theorem bodies are byte-identical.
The proof of private cbcEvaluationConstantTowerSquare uses the existing
ProEtaleRingRestrictionSquare.towerSquare_localization equation before applying
the generic localization-square lemma. Profiling found that the old implicit
conversion spent about ten seconds checking an unfolding of the full ringed
square. The generic helper now takes the termwise square used by that API,
rather than requiring an implicit expansion of the specialized square. Local
irreducibility attributes keep standard derived-category and functor records
compact during elaboration. The public cbcRealizationLimitMap_isIso proof
uses local witnesses from its existing proved existence theorems instead of
nested existential eliminations; no selected object enters an exported
definition. Two private component equations identify cbcSourceNatIso and
cbcTargetNatIso components with the published endpoint comparisons. The public
naturality proof uses these equations, so each endpoint construction is
normalized once. No comparison map or mathematical assertion changes.
The two owning definition nodes point to the foundation module. The additional
construction-interface node def-cbc-strict-tower-realization-comparisons records
the other extracted comparisons and proved auxiliary properties without any new
hole, giving the scalar-square node a definition dependency below its parent. The realization
node retains the two theorem declarations and records the actual proof. The
one new scalar/direct-image/limit theorem is a separate strictly smaller step.

## Users

The table includes every transitive consumer returned by tools/downstream.py
for the item and five redirected modules, plus those modules themselves.
Original public imports remain available through the foundation; none of these
consumers changes its mathematical assertions or needs a signature adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No source edit; same reexported API. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No source edit; same reexported API. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No source edit; same reexported API. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | No source edit; same reexported API. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompactSupportProjectionFormula | Y3 | No source edit; same reexported API. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompactificationOpenLimit | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompactificationPushLimit | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompactificationScalarData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | N2 | Retains theorem signatures; publicly reexports foundation; proves both identities. |
| Sheaf.Paper.CompletedOpenExchangeLimitNormalization | unclaimed | Import-only cycle repair; all declaration bodies and signatures unchanged. |
| Sheaf.Paper.CompletedOpenFiniteTransposeCoherence | unclaimed | Import-only cycle repair; all declaration bodies and signatures unchanged. |
| Sheaf.Paper.CompletedOpenScalarLimitSquare | unclaimed | Import-only cycle repair; all declaration bodies and signatures unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Import cycle repair and local irreducibility attributes; all declaration bodies and signatures unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateTranspose | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CompositionComparisons | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | F7 | No source edit; same reexported API. |
| Sheaf.Paper.ConstantTowerSquareNormalization | unclaimed | Import cycle repair and local irreducibility attributes; all declaration bodies and signatures unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FieldExtensionTowers | M3 | No source edit; same reexported API. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | U4 | No source edit; same reexported API. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | P9 | No source edit; same reexported API. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.NormalizedFieldPurityTrace | K4 | No source edit; same reexported API. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | J9 | No source edit; same reexported API. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | No source edit; same reexported API. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurIntegralCompletedCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurIntegralGeometricInputNormalization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurIntegralStrictCalculus | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurIntegralStrictReduction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurIntegralTotalUnitEquation | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurStrictIntegralExchangeData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalStalkExact | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | S5 | No source edit; same reexported API. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RelativeKunneth | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SemilinearExchangeDescentData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SemilinearExchangeReindexing | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | C5 | No source edit; same reexported API. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | M4 | No source edit; same reexported API. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | J5 | No source edit; same reexported API. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TensorHomExchange | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TowerGeometricPurityMate | M2 | No source edit; same reexported API. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VectorBundleThom | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | No source edit; same reexported API. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | No source edit; same reexported API. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | A9 | No source edit; same reexported API. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.CompletedOpenCartesianIdentity | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | E3 | No source edit; same reexported API. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.FiniteOpenCartesianCalculus | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenFactorExchangeRealization | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | No source edit; same reexported API. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | No source edit; same reexported API. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No source edit; same reexported API. |

## Status

landed 20261026T070353-L-3563540 2026-10-26 (merge of deliver/N2/Sheaf.Paper.CompleteProetaleStrictTowerRealization)
