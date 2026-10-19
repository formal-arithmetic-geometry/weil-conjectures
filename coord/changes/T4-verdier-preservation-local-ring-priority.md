# Sheaf.Paper.WeilVerdierPreservationStrata elaboration context

## Reason

The generic perfect-field preservation proof needs coherent Ring instances when its
coefficient ring is specialized to ULift of the finite coefficient quotient. The
retained profiler runs show a kernel deterministic timeout without this adjustment
at the generic-to-ULift specialization. Giving CommRing.toRing higher priority locally
aligns the inferred Ring with the parent of the inferred CommRing. This is a local
elaboration setting: it adds no instance declaration and exports no instance priority.
All three existing public signatures and the entire finiteStageDualizingComplex
construction are textually identical. All ring structures used are definitionally
identical to the original ones. No target statement or mathematical definition changes.
The original two holes are filled by proofs; no new hole is introduced.

One repeated public import line for IsConstructibleEtaleModuleSheaf is removed;
the identical retained line exports the same module. The four new imports are proof-only.
The complete public import set is identical before and after the delivery.

## Old

```lean
namespace WeilConjectures
```

The original file has no local registration of CommRing.toRing.

## New

```lean
namespace WeilConjectures

-- Align the lifted coefficient Ring instance with the generic CommRing theorem.
attribute [local instance 2000] CommRing.toRing
```

The registration ends with this file's namespace/section scope. Downstream instance
search uses its original priorities. Existing signatures and data constructions are
unchanged; the newly added helpers are private and used only by the two completed proofs.

## Users

All transitive importers reported by tools/downstream.py are listed below, with holders
read from the current claim records. No consumer is adapted. Source inspection finds
no external textual references to the three public declarations: the direct consumers
import the module as a proof dependency. The local priority is not exported, and both
previously available theorem types and the dualizing-complex data retain their meaning.
The partial single-file consumer sweep and its timeout are recorded in report.md;
only two of the nine original direct consumers completed that sweep.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.WeilVerdierPreservationStrata | T4 | Two holes proved; local priority aligns definitionally equal ring instances. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | D2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | Y6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | C8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | Y5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | R5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | U3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | R6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | Q4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | D6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | W3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | C6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | H1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | E6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | J7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | P8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | M1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | M4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | N3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | W7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | N4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | D9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | P1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | V4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | D4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | T8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | E4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | P9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Z9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | A7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | T3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | J3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | Y5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | F5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | N2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | U5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | C2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | J8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | E7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | C1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | V1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | P6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | W2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | B5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | M2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | R5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | P6 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | Y7 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | X8 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | Y5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public signatures, data and exported instance priorities unchanged; no adaptation. |

## Status

landed 20261019T132237-L-1206545 2026-10-19 (merge of deliver/T4/Sheaf.Paper.WeilVerdierPreservationStrata)
