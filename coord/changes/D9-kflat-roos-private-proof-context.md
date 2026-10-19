# SheafOfModules.KFlatRoos.representativeInvariance

## Reason

The completed proof uses scoped elaboration commands around private, proved helpers.
The static interface check classifies the new `omit` and `open` commands as an
interface change. This record documents their scope and the unchanged consumer API.
No existing public signature, visibility, definition, instance or public import changes.

## Old

After `roosMap`, the public `representativeInvariance` theorem had its existing
signature and proof `:= by sorry`. There were no helper-local elaboration commands
between these declarations. All earlier declarations were already proved by F7.

## New

The following commands apply only to the immediately following private declaration:

```lean
omit [HasCountableProducts (Modules R)] in
open MonoidalCategory in
private theorem categorical_kflat
```

```lean
set_option maxHeartbeats 400000 in
omit [HasCountableProducts (Modules R)] in
open MonoidalCategory in
private theorem level_quasiIso
```

The helpers convert the existing independent-coefficient K-flat predicate to
categorical K-flatness and prove tensor invariance by a K-flat resolution of the
coefficient module. Their bodies are complete proofs. Further private helpers prove
augmentation naturality and the derived roof comparison; they also have complete
proofs. The public theorem has its exact original signature and a complete proof.
Proof-only imports introduce these tools and the new generic, proved theorem
`CochainComplex.quasiIso_of_roos_coordinates`, whose module and DAG node are delivered.
No data are chosen from an unproved existence theorem by a new definition.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance
--uses representativeInvariance` finds no textual use outside the item. Its full
import closure is listed below. Only the item and the new generic lemma module
are delivered; none of these existing consumers needs adaptation. The new commands
are scoped to private proofs and cannot change a target's meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance | D9 | Own proof; signatures and public imports preserved. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | C7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | U5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeart | X8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.DerivedNakayama | U6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | T3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | U4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | W7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | C1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | V4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | C2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | X3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | C5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | D4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | N1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | N3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | J2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | F2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | U2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | Y5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | H2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Z5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | G2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | C1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | J1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | Q6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | N1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | E3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | M6 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | R9 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Z8 | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | B4 | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | C1 | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | C3 | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | D2 | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |

## Status

landed 20261019T093336-L-2297557 2026-10-19 (merge of deliver/D9/Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance)
