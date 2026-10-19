# DerivedPullbackCompositionMonoidal local instance priority

## Reason

The proof specializes the generic source-library monoidal coherence equations to module
coefficients. A local priority override selects the braided structure supplied by the existing
symmetric structure, aligning elaboration with the generic coefficient-category helper.
The stage-3 static checker flags an added attribute command conservatively as an interface
change, so this record documents its scope and consumer check.

## Old

The file had no local override for `SymmetricCategory.toBraidedCategory`.
The existing namespace-opening command was:

```lean
namespace AlgebraicGeometry.Etale
```

## New

The same namespace contains a proved private tensor-composition helper and this exact command
before the existing public theorem:

```lean
attribute [local instance high] SymmetricCategory.toBraidedCategory
```

Every existing public declaration, its visibility, all six public imports and the complete
written signature of `AlgebraicGeometry.Etale.canonicalDerivedPullbackCompositionMonoidal`
are unchanged. The attribute is local to this file; it is not exported to consumers.
A separate scratch module imports the proved module, repeats the original theorem signature
without this attribute and proves it by applying the delivered theorem. This compiles in
5.3 seconds, checking that the elaborated types agree as well. The delivered module itself
compiles cleanly in 11.2 seconds. No definition or target statement changes.

## Users

The source-import graph lists the following transitive consumers; their existing statements
and proofs need no adaptation because the public interface is preserved and the priority
override is local. No consumer file is included in this delivery. Holder entries reflect the
shared claim records at preparation time. `tools/downstream.py` was also started as required, but its process was killed by the
environment before it produced a result. This table was independently prepared by reading
all source imports in the two library roots and taking their transitive consumer closure.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CompactProjectionExchange | W4 | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportProjectionOpenRestriction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericStratumMate | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericFibreVanishing | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | V3 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.KunBcKunnethCompat | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Unchanged public interface; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | F6 | Unchanged public interface; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged public interface; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged public interface; no adaptation. |

## Status

landed 20261019T002532-L-2149520 2026-10-19 (merge of deliver/E4/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal)
