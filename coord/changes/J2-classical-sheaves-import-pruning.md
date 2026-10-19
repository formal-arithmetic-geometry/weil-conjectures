# AlgebraicGeometry.proEtaleClassicalSheaves

## Reason

Prove the recognizing-classical-sheaves theorem using its three detailed dependencies.
Remove two redundant public imports: ClassicalDerivedDefinitions already publicly
imports both of them, so the available public declarations and instances are unchanged.
No definition, theorem signature, visibility, target statement or target meaning changes.
The finite-coefficient theorem is unnecessary because the arbitrary-coefficient module
comparison identifies the essential image for every commutative ring, and the resulting
full-subcategory equivalence preserves finite limits and colimits.

## Old

```lean
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.SixFunctors.ClassicalDefinition
```

## New

```lean
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
```

The retained public import Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions publicly
imports both removed public modules. The new proof import supplies filtered-colimit
preservation by the forgetful functor from modules to sets. The removed private
ClassicalDefinition import defines intrinsic arbitrary-ring predicates unused by this
fixed-commutative-ring theorem; it exposed nothing to importers.

## Users

The current source scan finds 6 direct importers:
- Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison
- Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison
- Sheaf.Paper.AdicConstructibleFiniteReductions
- Sheaf.Paper.DegreeZeroCompactSupportSections
- Sheaf.Paper.EtaleLocalMonodromyRealization
- Sheaf.Paper.LocalizingClosureCtfEqualsBc

The prescribed downstream scan finds 323 transitive importers.
No other module text uses proEtaleClassicalSheaves. The removed public imports
remain public through ClassicalDerivedDefinitions, so no consumer needs adaptation.
The private helper is proved and introduces no global instances. Claim holders below
are a source-snapshot observation on 2026-10-19; no consumer is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves | J2 | Theorem proof and redundant imports change. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | K8 | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | Y8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicResidueLissePerfectLift | V6 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicStratifiedPerfect | P5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeart | X8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | Y5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | P8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | C5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | U9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteComparisonLocalizing | V7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | W5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | Q9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | M2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | V4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | H7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UnboundedLocalizingPullback | Y7 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | X9 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | Public interface unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | N1 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | A2 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Public interface unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public interface unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public interface unchanged; no adaptation. |

| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public interface unchanged; no adaptation. |

## Status

landed 20261019T005304-L-2748777 2026-10-19 (merge of deliver/J2/Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves)
