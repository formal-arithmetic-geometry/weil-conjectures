# AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects proof commands

## Reason

The preflight interface check detects the additional namespace openings for the two
private proved comparison helpers. The ordinary proof imports, private helpers and
namespace openings serve elaboration of the completed proof. Every existing public
signature, public import and declaration visibility is unchanged. There is no new
public definition, notation, instance or attribute. No consumer needs adaptation,
and no definition used by a target or target statement changes meaning.

## Old

```lean
open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
```

The module had no declaration-local namespace openings.

## New

```lean
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
```

Before the private lemma `free_hasConstantModel`:

```lean
open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
```

Before the private lemma `constantModel_eq_of_localFree`:

```lean
open MonoidalCategory MonObj in
```

The two declaration-local openings end with their respective private lemmas.
The only existing public declaration is `coefficient_finite_descent_objects`; its
signature, universes and visibility remain verbatim identical. Its proof is now complete.

## Users

Computed with `python3 tools/downstream.py Sheaf.Paper.CoefficientFiniteDescentObjects
--uses AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects`. The scan found
335 transitive consumers. The only textual declaration user outside the item is
`Sheaf.Paper.FiniteCoefficientDescentTwoColimit`, which uses the identical theorem
signature. None of the consumers is edited; their holders were not queried because
there are no forced adaptations or public signature changes. All are listed below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientFiniteDescentObjects | F3 | Existing signature unchanged; proof completed. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteTorStability | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteWindow | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralModels | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperHeartBound | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.PurityChernClasses | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.RestrictionLocal | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.SfBidualityClass | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.VerdierExchange | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.WeilOne | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Targets.PoincareUncurry | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | Not queried; unchanged | Same public API; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not queried; unchanged | Same public API; no adaptation. |
| TargetsCheck | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.Statement | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Basic | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.TraceFormula.Statement | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not queried; unchanged | Same public API; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | Not queried; unchanged | Same public API; no adaptation. |

## Status

landed 20261019T192720-L-1858666 2026-10-19 (merge of deliver/F3/Sheaf.Paper.CoefficientFiniteDescentObjects)
