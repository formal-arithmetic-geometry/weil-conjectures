# AlgebraicGeometry.Etale.closedImmersion_coprojection

## Reason

Preflight requests a change record for new `variable`, `open`, and `attribute` commands.
These commands only support a private generic proof helper. No existing signature,
public definition, public import, or mathematical statement changes. All new proof
imports are private. The theorem closes its original hole by the source's Hom/projection
argument and its four cases retain the original hypotheses and conclusions.

## Old

The original proof was `:= sorry`. Its namespace setup was:

```lean
universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
```

## New

The namespace setup adds `MonoidalCategory` to its `open` command so the private
helper can name monoidal structures. This changes name resolution within this file
only. Immediately inside that namespace the private helper has this local setup:

```lean
section General

universe v

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

attribute [local instance] Sheaf.monoidalCategory
```

`end General` closes the section immediately after the private definition
`coprojectionOfProjection`. Its variables are bound only into that helper; the local
instance attribute expires at the section end. The next private helper is
`ambientCoprojection`. The existing public theorem has exactly its original signature.
Consequently no target statement or definition used by a target changes meaning.
No declaration from the private helpers is used in any public signature or definition.
The original theorem's proof is complete and compiled in 14.2 seconds with no warnings.

## Users

The table lists the source import closure (read-only import scan, matching the
`tools/downstream.py` query). There is one direct importer,
`Sheaf.Paper.EtaleGeometricBiduality`, and none mentions the theorem name in code.
All downstream effects are uniform: only the proof of an unchanged theorem changes,
and the section-local setup exports no new instance. No consumer is edited or adapted.
Current holders are recorded from claim metadata at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleClosedCoprojection | B5 | Private proof setup only; signature unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | P9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | F9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | C8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityObjects | W9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicSectionClosedSupport | Y5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | R5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportCondensedRealization | U3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | R6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportPerfectness | Q4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactSupportUniformTorBound | D6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | Y9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | J4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | C6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ConstructibleHomComparison | H1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.EtaleGeometricBiduality | G1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FieldShriekCompositionQcqs | P8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientHomChange | M1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteConstructibleHom | M4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | N3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteProperLocalizing | W7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteStageVerdierBiduality | N4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | X3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | A5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | D9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleInternalHom | P1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IteratedWeilCocycle | D4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.LocalFrobeniusConjugacy | Q5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | A6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | T8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperCoincidenceFrobenius | T6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperCompactCoincidence | P9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperHeartBound | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | T7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.PurAdicReconstruction | H8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.PurityDncInvariance | H2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RationalRestrictionGlue | Z9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RationalStalkExact | A7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.RestrictionLocal | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SfBidualityClass | C6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | T3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityMap | R2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityTowerBound | J3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SmoothTrace | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | N2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceCompactificationCohomology | U5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFixedScheme | C8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TraceGraphCorrespondence | A3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TrfDevissageGeneration | C2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TwConventions | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.VerdierExchange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WeilFourierInversion | J6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WeilOne | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WeilOpenImageDelta | E7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | S2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | C1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | V1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | P6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | W2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | M7 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.RationalVerdier | V4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | E4 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | P6 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | X8 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | Y5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.Statement | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No change to signatures, visibility, statements or definitions; no adaptation needed. |

## Status

landed 20261019T093255-L-2287644 2026-10-19 (merge of deliver/B5/Sheaf.AlgebraicGeometry.EtaleClosedCoprojection)
