# AlgebraicGeometry.ProEtale.coefficientHeart_essentiallySmall

## Reason

The proof adds private generic smallness lemmas with additional universe variables and opens
`CategoryTheory.Limits`, `CategoryTheory.Obj` and `CategoryTheory.MonoidalCategory` to write
those proofs. The delivery gate conservatively treats these file commands as an interface
change, so this record enumerates their consumers. All existing public imports, declaration
signatures and visibility are identical. The additional helpers are private proved theorems;
no public definition is introduced or altered. No target statement or its definitions change.

## Old

```lean
universe u

open CategoryTheory
```

The original module contains no later `universe` or `open` commands.

## New

```lean
universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
```

Before `smallFromRestrictions`:

```lean
universe u' v'
```

Before `finitelyPresentedSmall`:

```lean
open CategoryTheory.MonoidalCategory
```

These commands supply universe names and unqualified notation while this module elaborates;
they do not add binders to the existing public theorem. The theorem signature was compared
verbatim with the current source and remains identical. Its only change is the completed proof.
The public imports also remain identical. No user requires an edit. The proof-only imports
are listed in report.md, including the `import all` needed for the proved private detection
lemma; none is a public import.

## Users

Computed with `python3 tools/downstream.py Sheaf.Paper.CoefficientHeartSmall --uses
AlgebraicGeometry.ProEtale.coefficientHeart_essentiallySmall`. The tool reports the module
itself as the only textual use of that full declaration name; all transitive importers are
listed below as well. Holder snapshot: 2026-10-19. No consumer module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientHeartSmall | F3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CoefficientFiniteDescentHom | E4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CoefficientHeart | X8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ConstructibleCompactness | U7 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ConstructibleExtContinuity | U8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | P8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.DetIndHeartIISums | C5 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteWindow | W5 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteWindowBounded | C1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FormalClosedSupport | Q9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FormalClosedSupportII | M2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IndConstructibleExtensions | K4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IndConstructibleFilteredColimits | M1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IndHeartCanonicalPresentation | W8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IndHeartFullFaithfulness | M2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralModels | D4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.MateOpenRestriction | D7 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperHeartBound | K5 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.RestrictionLocal | R3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.SmoothTrace | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.UniformConstructibleExt | X9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.VerdierExchange | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.WeilOne | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.FieldTensor | N1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | No signature or elaboration change; no adaptation needed. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No signature or elaboration change; no adaptation needed. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No signature or elaboration change; no adaptation needed. |
| TargetsCheck | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.Statement | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No signature or elaboration change; no adaptation needed. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No signature or elaboration change; no adaptation needed. |

## Status

landed 20261019T002542-L-2152031 2026-10-19 (merge of deliver/F3/Sheaf.Paper.CoefficientHeartSmall)
