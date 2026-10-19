# AlgebraicGeometry.Scheme.stratumScalarExtension

## Reason

Record the proof-support commands flagged by stage-3 preflight: the additional
`Opposite` opening, two elaboration transparency options, and section-local variables
used in private helpers. No existing public declaration, definition body, visibility,
or public import changes. The added bridge theorem is proved in a new module with
its own node; the item imports that module privately.

## Old

The original file-level proof context was:

```lean
@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme
```

The three public definitions and the theorem signature are retained verbatim.
The theorem body was `:= by sorry`.

## New

```lean
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme
```

The two nested helper sections introduce variables for private declarations only;
both sections end before the original public theorem. The theorem has a complete
proof. Private helpers and extra openings do not occur in any public signature.
Elaboration options and openings have file-local effect. There is no new notation,
attribute registration or public instance. All original public imports remain.
The new public bridge is
`AlgebraicGeometry.Scheme.proEtaleAlgebraicInverseImage_exists`, with its complete
signature in node `lem-sp-proetale-algebraic-inverse-image`; there were no consumers
of that previously absent module. It is imported privately by this item.

## Users

`tools/downstream.py Sheaf.Paper.StratumScalarExtension --uses
AlgebraicGeometry.Scheme.stratumScalarExtension` enumerated the following import
closure. Its textual declaration search found the name only in the item itself.
Every original public declaration signature and definition body was compared with
the current sources and is identical. Consequently all listed consumer statements
and definitions keep the same meaning, including the targets. No consumer needs an
adaptation or a new statement review. Holders of untouched consumers were not
queried, because this delivery edits none of them.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.StratumScalarExtension | W2 | complete proof; unchanged signature and definitions |
| Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage | W2 (new module) | proved bridge; no prior consumers |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.DeligneLaumon.Reduction.Composition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicPurityExceptionalReduction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicPurityFiniteTensor | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicPurityObjects | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicPurityRootComparisons | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicPuritySourceReduction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicPurityTwistReduction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicSectionClosedSupport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AffineCurveHcZero | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AffineSpaceRationalInduction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ArithmeticRoots | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BasicOperationsCoefficientReduction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BoundaryDualizingComposition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BoundaryQFoundation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BoundaryQMaps | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BoundaryQTransport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.BrownExceptionalAdjoint | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CartierClassAgreement | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ChernFlagFormula | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ClopenStrictSystemComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CoefTowerCoaugmentation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CohomologicalSmoothComposition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CommonStageFourierTransform | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CommonStageWeilFourierTransform | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CommonStageWeilShriek | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactFiberStalk | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportCoefficientAction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportFiniteAction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportLerayFiltration | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportPerfectness | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportReductionTower | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactSupportUniformTorBound | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactificationCoherenceCocycle | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactificationLocalizing | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompactificationRefinementLocalizing | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ConnectedConstantH0 | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ConstructibleHomComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CoprojectionCompositionMate | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CurveIntermediateExtension | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DenseOpenPiOneSurjective | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DirectImageChangeRingTranspose | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DirectImagesConstructible | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DlConstantFieldCharts | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DlConstructibleFibresExact | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.DualizingObjectPurity | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleRhoMonoidalMate | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.EtaleWeilSheafEquivalence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ExceptionalFiniteRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ExceptionalProEtaleRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ExceptionalSiteRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FieldShriekCompositionQcqs | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FieldShriekLowerBound | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FieldWeilShriekShiftData | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteBoundaryWeights | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteClosedShriek | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteCoefficientHomChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteCompactSupportConstructibility | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteConstructibleHom | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteEtaleDescent | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteProductCompactification | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteReductionAffineOrientation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteReductionChartCalculus | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteReductionComparisons | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteReductionOfPurity | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteReductionRootCharts | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteStageVerdierBiduality | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FiniteTorStability | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FlagPullbackInjective | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FourierKernelConvolution | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FourierTraceFormula | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusCompactSupportExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusGeometricExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.FrobeniusSquareExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralConstructibleInternalHom | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralDirectImageTower | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralExceptionalInverseImage | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralPointTransportTowerPowers | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralProperBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralProperDirectSums | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralProperProjectionFormula | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.InterchangeProperPasting | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.InternalHomPullback | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IteratedWeilCocycle | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.IteratedWeilMap | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.LisseDenseOpenRecovery | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.LisseExtensionInertia | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.LocalFrobeniusConjugacy | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.LocalizingLowerShriekComposition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.MateOpenRestriction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.MiddleExtensionHcZero | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.MixedReductionUnit | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ModelCompactComparisonUnit | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.OrdinaryCompactCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PoincarePointFiniteness | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PointCompletedEvaluation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProjectiveBundleFormula | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperBaseChangeRational | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperCoincidenceFrobenius | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperCompactCoincidence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperExceptionalRestriction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperHeartBound | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperUnboundedCoproducts | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperUnboundedWindow | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ProperUnboundedWindowIso | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurAdicReconstruction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityAffineLineOrientation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityChernClasses | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityCompositionCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityCoprojection | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityDiagonalDualizingObject | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityDiagonalSectionPasting | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityDivisorClass | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityDncComparisons | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityDncFamilyIntrinsic | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityDncInvariance | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityFrameIndependence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityGysinStructure | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PuritySourceTransports | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.PurityTwistCancellation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.QbarPerverseSubcategories | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.QcqsCompactSupportRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RationalExceptionalRestriction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RationalPurityPresentation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RationalRestrictionGlue | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RationalSmoothPurityCanonical | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RationalStalkExact | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RealBoundaryPathIndependence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RealSheafSections | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RegularImmersionPurityComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RelativeSupportBottomDescent | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RelativeSupportCoordinateModel | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.RestrictionLocal | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SfBidualityClass | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SfPreservationClass | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SfProEtaleProjectionFormula | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothMateCounitCancellation | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothPurityMap | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothPurityQbar | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothPurityTowerBound | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothPurityTowerReconstruction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SmoothTrace | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SupportedProjectionSplitting | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.SystemOperationExchangeRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TateTwistSupportCondition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TensorTraceTranspose | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceBaseChangeSecond | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceCohomologicalCorrespondence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceCompactificationCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceFixedScheme | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceFormulaAdicSystem | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceFormulaCoefficientConventions | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceFormulaDualizingComplex | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceGraphCorrespondence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TraceTransposeBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TrfDevissageGeneration | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TrfWitnessedOpenPullback | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.TwConventions | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.UnboundedBaseChangeExtension | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.VaryingRingGraphSummand | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.VerdierExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilCompactSupportCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilFourierInversion | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilFourierPlancherel | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilMixedUpperBounds | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilOne | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilOpenImageDelta | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.WeilShriekShiftCompatibility | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Paper.ZlShriekComposition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.OpenScalarExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.BoundaryDualityDischarge | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.CompactCoefficientComposition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.FiniteDualizing | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.FrobeniusFixedPoints | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.GeneratorReductionStatement | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralDualizing | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralOperationShiftData | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralSystemOperations | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.IntegralVerdier | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.InternalHomPullback | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.OpenAdjunctionShift | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.OpenFactorCoherence | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.OpenFactorPullModel | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.OpenFactorTensorModel | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.RationalOperations | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.RationalVerdier | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.SmoothPurity.NormalizedWitness | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Targets.AffineSpaceRationalLine | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Targets.PoincareUncurry | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.Targets.SmoothPurityQbar | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not queried; untouched | no interface or meaning change; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried; untouched | no interface or meaning change; no adaptation |
| TargetsCheck | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.FourierTransform.Perverse | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.PoincareDuality.Poincare | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.PoincareDuality.ProjectionFormula | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.PoincareDuality.Verdier | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.SmoothPurity.Defs | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.Statement | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Basic | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Basic | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Main | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.TraceFormula.Statement | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.Curve | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.Finiteness | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.LFunction | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.LocalizationRational | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.PoincareDuality | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.RealPurity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.Examples | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.Rationality | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.TraceFormula | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; untouched | no interface or meaning change; no adaptation |
| WeilConjectures.ZetaFunction.Weights | not queried; untouched | no interface or meaning change; no adaptation |

## Status

landed 20261019T112603-L-3958856 2026-10-19 (merge of deliver/W2/Sheaf.Paper.StratumScalarExtension)
