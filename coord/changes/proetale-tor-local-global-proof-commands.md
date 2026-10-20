# ProEtaleTorLocalGlobal proof commands

## Reason

Preflight requires a record for new command blocks. The added proof-helper section
uses local elaboration options to handle the existing coefficient-sized derived
categories and tensor isomorphisms. It closes before the geometric refinement
helpers and the unchanged public statement. All new helper declarations are private,
fully proved theorems. No existing statement, definition body, public import,
instance or attribute changes. All target meanings are preserved.

## Old

The original file has the existing header commands:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
```

After `end CategoryTheory`, it opens the public theorem's namespace directly:

```lean
namespace AlgebraicGeometry.Scheme
```

## New

The original header commands remain verbatim. Between the existing definition and
the existing theorem, the delivery adds this closed proof-helper section:

```lean
section ProofHelpers
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MonoidalCategory
namespace CategoryTheory
```

The three private proved lemmas are followed by:

```lean
end CategoryTheory
end ProofHelpers
namespace AlgebraicGeometry.Scheme.ProEt
```

The finite-refinement private theorems are followed by:

```lean
end AlgebraicGeometry.Scheme.ProEt
namespace AlgebraicGeometry.Scheme
```

The private coefficient-site finite-cover theorem closes that namespace before
reopening the original namespace for the existing public theorem. The
`coefficientModelSliceRestriction` definition and the public theorem's signature
remain verbatim. Only private theorem proofs use the new local settings; the
settings and namespace openings do not export any notation, instance or attribute.

## Users

Both `tools/downstream.py` checks with `--uses coefficientModelSliceRestriction`
and `--uses hasFiniteCoefficientProEtaleTorAmplitude_iff_locally` find only this
module as a textual user. The complete transitive-importer inventory is below.
Each keeps identical public declarations and imports. None requires adaptation.
Current claim holders are recorded at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal | J5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | A2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | V7 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | A6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | C7 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | R1 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | N3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | D3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | E6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | M3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Q1 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | W7 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | R3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | V9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | R5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | M5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | C5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | C2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralModels | D4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | V4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | C2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | N3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | J2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | X9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | Y5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | N2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | Z9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | X8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | B2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | D9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | M9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | J5 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | T8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | P6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | G8 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B2 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| TargetsCheck | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.Statement | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Identical existing signatures, visibility and definitions; no adaptation. |

## Status

landed 20261020T051419-L-1672942 2026-10-20 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal)
