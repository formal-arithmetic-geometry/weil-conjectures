# Sheaf.Paper.IntegralConstantModelHeart proof context

## Reason

Repair the returned global-build failure of C2/Sheaf.Paper.IntegralConstantModelHeart
(landing fcb0af3f45, repair job 223e368e86632539). The previous final conjunction
exceeded 200000 heartbeats while elaborating bounded_tri. The large definitions
upperStarFromPoint and CondensedRing.upperStar were also repeatedly unfolded by
coefficient-transport proofs. Keep those definitions locally irreducible, and assemble
the heart properties over an abstract coefficient ring in the proved private
general_heart helper before specializing to the integral coefficient object.
The smallness proof explicitly unfolds upperStar once where its definition is needed.
No limit is increased, no proof is admitted, and no definition is replaced or split.

## Old

```lean
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
```

The module declared integralHeartCoefficientRingObj unchanged and the theorem
integralConstantModelHeart with proof `by sorry`.

## New

Both public declarations keep their exact signatures, and the coefficient abbreviation
keeps its exact body. Proved private helpers implement coefficient-isomorphism transport,
zero and isomorphism closure, triangulation, truncations, the degree-zero heart,
abelianness and essential smallness. They use local sections, extra private universes,
MonoidalCategory/MonObj/CondensedRing and Obj/ZeroObject scopes. Three private sections use:

```lean
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
```

These attributes end with their sections. Only private proof imports change. The new
IntegralCoefficientRingComparison module proves its theorem by constructing the
isometric integer-ring equivalence and its maps on continuous functions; it has zero holes.

## Users

Current tools/downstream.py reports 302 transitive consumers, listed below. Its name
search finds integralHeartCoefficientRingObj only in this module and
Sheaf.Paper.IntegralConstructibleHeart. Every consumer sees identical public declarations,
coefficient data, and public imports. No consumer source adaptation or target re-review
is needed: the change affects proofs and their local elaboration context only.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralConstantModelHeart | G2 | Private proofs and local attributes changed; public interface preserved. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | claimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public interface and coefficient data unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public interface and coefficient data unchanged; no adaptation. |

## Status

landed 20261019T192736-L-1861859 2026-10-19 (merge of deliver/G2/Sheaf.Paper.IntegralConstantModelHeart)
