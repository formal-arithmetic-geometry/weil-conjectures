# AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived

## Reason

Prune proof-only dependencies from the completed theorem. The theorem signature,
all definitions, and the retained public support-sheaf imports are unchanged.
Several old public imports were only needed by the former resolution proof and
are redundant: all four remain publicly re-exported by the retained
CondensedClosedSupportAdjunction import. This record documents the syntactic
public-import change flagged conservatively by the stage-3 checker.

## Old

The module publicly imported:

```lean
public import Sheaf.Paper.FormalClosedSupportSheaves
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
```

## New

The module publicly imports only:

```lean
public import Sheaf.Paper.FormalClosedSupportSheaves
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
```

The proof now uses proof-only imports for additive and unique adjunctions,
triangulated categories, and Noetherian schemes. The removed direct derived-functor
and Grothendieck-category imports remain available through the retained
CondensedClosedSupportAdjunction module, whose public imports list all four
verbatim. Consequently the full public import closure is retained.

## Users

The read-only `tools/downstream.py Sheaf.Paper.FormalClosedSupportDerived --uses formal_closed_support_derived` query lists 275 transitive consumers and the item itself as the sole declaration-use match. All are listed below. Claim holders were read from coord/claims on 2026-10-19. The retained CondensedClosedSupportAdjunction publicly imports all four removed direct public imports. Consequently every consumer retains access to the same declarations, and its statements and definitions keep their meanings. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FormalClosedSupportDerived | W5 | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3 | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Same public closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Same public closure; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same public closure; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Same public closure; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Same public closure; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Same public closure; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Same public closure; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Same public closure; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Same public closure; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | Same public closure; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | Same public closure; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Same public closure; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Same public closure; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Same public closure; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Same public closure; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Same public closure; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | Same public closure; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | C5 | Same public closure; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | Same public closure; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Same public closure; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Same public closure; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Same public closure; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteWindow | W5 | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Same public closure; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Same public closure; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | Q9 | Same public closure; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | M2 | Same public closure; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | Same public closure; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | Same public closure; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | Same public closure; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | Same public closure; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | Same public closure; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | Same public closure; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralModels | D4 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | K1 | Same public closure; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | Same public closure; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Same public closure; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Same public closure; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Same public closure; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Same public closure; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Same public closure; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Same public closure; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Same public closure; no adaptation. |
| Sheaf.Paper.ProperHeartBound | K5 | Same public closure; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | Same public closure; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Same public closure; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Same public closure; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | Same public closure; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | Same public closure; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Same public closure; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Same public closure; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Same public closure; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Same public closure; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Same public closure; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Same public closure; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | X9 | Same public closure; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | Same public closure; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | Same public closure; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same public closure; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same public closure; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same public closure; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | B8 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Same public closure; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same public closure; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Same public closure; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same public closure; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same public closure; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same public closure; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same public closure; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same public closure; no adaptation. |
| TargetsCheck | unclaimed | Same public closure; no adaptation. |
| WeilConjectures | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same public closure; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same public closure; no adaptation. |

No target statement or target-used definition is changed, so no target-statement
review is reopened. The only changed Lean module is the item held by W5.

## Status

landed 20261019T034339-L-423813 2026-10-19 (merge of deliver/W5/Sheaf.Paper.FormalClosedSupportDerived)
