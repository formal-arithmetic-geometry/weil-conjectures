# AlgebraicGeometry.ProEtale.proEtale_closed_localization

## Reason

The statement only needs fixed-ring module coefficients and the existing pro-etale
restriction/pullback/direct-image API. The finite continuous-function coefficient
operations and derived realization machinery are unnecessary. Replace their public
import by the concrete coefficient instances, and import weakly etale base change
privately for the proof. The theorem signature and every definition stay unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
```

## New

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
```

## Users

The successful `tools/downstream.py` invocation on resuming reported 490 transitive
importers and no downstream uses of the theorem. A repeated inventory refresh waited
without returning and was stopped. The table below was refreshed independently by
searching source import lines with `rg` and taking their reverse transitive closure;
it initially contained 495 modules. A fresh source inventory on the current resume
contains 505 modules, with the same two direct private importers. The table includes
all current consumers and the earlier snapshot rows. Their claim holders were not queried because
none is adapted. No delivery or checking tool was changed.

The two direct importers are ClosedInverseImageLimits (D7) and
IntegralConstructibleBoundedBelowCompactness (X2); both import this module privately.
The former supplies its own statement imports; the latter explicitly imports
ProEtaleFiniteCoefficientDirectImage as well. Thus the removed public import is not
re-exported across either boundary. Both original consumer files compiled cleanly
against this delivery in a scratch-only overlay (2.9s and 3.7s respectively).
Statements and exported definitions of every transitive importer are unaffected.
No consumer is edited or forcibly adapted. The table lists the complete source
import closure; claim holders are a read-only snapshot, with no adaptation claim.

| module | group holding it | effect |
| --- | --- | --- |
| Comparator.Weil.Solution | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits | D7 | Direct private import; own statement imports. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts | V7 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Compactification.NagataDensityNormalization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CondensedERealization | Y9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DetIndHeartIISums | C5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteWindow | W5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FormalClosedSupport | Q9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FormalClosedSupportDerived | W5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FormalClosedSupportII | M2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unqueried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | X2 | Direct private import; explicitly imports removed coefficient module. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralExtensionByZero | A3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralModels | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | H8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.MateOpenRestriction | D7 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperHeartBound | K5 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RealSheafSections | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RestrictionLocal | R3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.SmoothTrace | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.UniformConstructibleExt | X9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.VerdierExchange | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilOne | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive private import boundary; exported interface unchanged. |
| TargetsCheck | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.Statement | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive private import boundary; exported interface unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalRealizationTensorComparison | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.SixFunctors.GeneratorReductionStatement | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.GlobalGeometricFrobenius | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |
| Sheaf.Paper.LocalizedTopChern | not queried; no adaptation | Transitive private import boundary; exported interface unchanged. |

## Status

landed 20261019T005431-L-2770633 2026-10-19 (merge of deliver/T8/Sheaf.AlgebraicGeometry.ProEtaleClosedLocalization)
