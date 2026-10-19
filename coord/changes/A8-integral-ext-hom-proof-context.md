# AlgebraicGeometry.ProEtale.CondensedRing.integralExtHomContinuous

## Reason

The proof uses the scoped zero-object notation to apply bounded triangulated
devissage. The static delivery checker classifies the extra `ZeroObject` scope
and declaration-local `omit`/elaboration commands as a context change. This record
documents that context. All three public imports, the declaration signature and
visibility, and every existing definition remain unchanged. Proof imports are
private. The two unused characteristic instances were already absent from the
elaborated original theorem; `omit` explicitly maintains that binder behavior.
The elaboration options apply only to this theorem.

## Old

```lean
open scoped CategoryTheory.Obj

theorem integralExtHomContinuous
    {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)))
    (hC : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)) ℤ)
    [HasColimit K]
    (b : ℤ) (hK : ∀ i : I, ∀ r : ℤ, r < b → IsZero ((K.obj i).X r)) (q : ℤ) :
    IsIso (homContinuityComparison (K ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.mapCocone (colimit.cocone K)) C q)
```

## New

```lean
open scoped CategoryTheory.Obj ZeroObject

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 150000 in
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
theorem integralExtHomContinuous
    {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)))
    (hC : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)) ℤ)
    [HasColimit K]
    (b : ℤ) (hK : ∀ i : I, ∀ r : ℤ, r < b → IsZero ((K.obj i).X r)) (q : ℤ) :
    IsIso (homContinuityComparison (K ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.mapCocone (colimit.cocone K)) C q)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralExtHomContinuity | A8 | Item proof completed; identical signature. |

Source-only `tools/downstream.py --uses` reports 298 downstream modules and
three consuming modules, all listed below. No source adaptation is made to any
of them. Claim ownership is unaffected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ArithmeticRoots | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ChernFlagFormula | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteTorStability | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FlagLocalComparison | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.FourierTraceFormula | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | Not adapted; claim unaffected | Direct theorem consumer; identical signature, no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | Not adapted; claim unaffected | Direct theorem consumer; identical signature, no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | Not adapted; claim unaffected | Direct theorem consumer; identical signature, no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.LocalizedTopChern | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.MateOpenRestriction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.PurityChernClasses | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.RestrictionLocal | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.SfBidualityClass | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.VerdierExchange | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.WeilFourierInversion | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.WeilOne | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Paper.ZlShriekComposition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.RationalOperations | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Targets.PoincareUncurry | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| TargetsCheck | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.SmoothPurity.Defs | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.Statement | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Basic | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.TraceFormula.Statement | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.Curve | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.Examples | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
| WeilConjectures.ZetaFunction.Weights | Not adapted; claim unaffected | Transitive importer; identical public interface, no adaptation. |
No consumer needs an adaptation: the public imports, elaborated signature and
canonical comparison map are identical. No target definition changes meaning.

## Status

landed 20261019T192645-L-1851874 2026-10-19 (merge of deliver/A8/Sheaf.SixFunctors.IntegralExtHomContinuity)
