# SheafOfModules.derivedScalarExtension_counitShift

## Reason

Prune two unused public imports from
`Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift`. Neither supplies a
notion needed by the unchanged theorem signature or a step of its proof.
The ordinary functor is additive by hypothesis, and the ringed-site interfaces
already supply the topology and module categories appearing in the statement.

## Old

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.SiteCoveringAxioms
```

## New

Both public import lines are removed. The theorem signature is unchanged.
The proof imports the separate-universe change-of-rings model privately:

```lean
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
```

## Users

The current source scan (`tools/downstream.py` with the item module and
`--uses derivedScalarExtension_counitShift`) finds 357 downstream modules, with
no use of the theorem outside its own declaration. The two direct importers are
`Sheaf.Algebra.Homology.ScalarExtensionUnitTriangles` and
`Sheaf.SixFunctors.EtaleHomThickLocus`; both import the item privately.
The former explicitly publicly imports `SiteCoveringAxioms` and the sheaf tensor
interface. The latter gets its public tensor and topology interfaces from its
own public imports. Neither refers to an auxiliary declaration of the removed
imports. Their signatures therefore retain the same meanings and require no
adaptation. Because both edges into the item are private, its public-import
removals cannot alter any indirect user's public import closure.
A separate lcompile.py --all check compiled the delivered item and both unchanged
direct importers together with exit code 0 (0.0, 0.0 and 1.4 seconds).
The table lists the full downstream scan and current holders at this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift | T1 | Identical theorem signature; complete proof. |
| Sheaf.Algebra.Homology.ScalarExtensionUnitTriangles | T2 | Private importer; compiled unchanged against pruned imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AdicTorFlatCohomology | S6 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.LevelwiseAdicTruncations | S9 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.MateOpenRestriction | D7 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PotentialRegularBaseChange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperHeartBound | K5 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperOpenCoefficientMate | X5 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.RestrictionLocal | R3 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SmoothTrace | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TwConventions | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.VerdierExchange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.WeilOne | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.EtaleHomThickLocus | S2 | Private importer; compiled unchanged against pruned imports; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenTensor | E6 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Indirect user behind a private import; no interface change. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Indirect user behind a private import; no interface change. |
| TargetsCheck | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.Statement | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Indirect user behind a private import; no interface change. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Indirect user behind a private import; no interface change. |

No definition or target statement changes, and no target meaning review is reopened.

## Status

landed 20261019T034306-L-418251 2026-10-19 (merge of deliver/T1/Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift)
