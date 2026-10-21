# AlgebraicGeometry.ProEtale.CondensedRing.FormalClosedSupportAssertions

## Reason

Restore the assigned quarantined module at its original path and fill its theorem.
The archived structure no longer elaborates against the current derived functor API:
`rightAdjoint`, `rightAdjoint_eq`, and `fiber` fail to synthesize
`PreservesFiniteColimits (lowerStar Λ i)`. The preceding `ordinaryAdjunction` already
proves this exactness by `ordinaryAdjunction.leftAdjoint_preservesColimits`.
Introduce that local instance inside each affected field type. This adds no hypothesis,
changes no functor, and preserves all mathematical assertions and normalization equations.
The theorem's signature and all public imports stay verbatim. No source-library module
is edited. Targets using this assertion may be reviewed for this explicit typeclass
context repair; their mathematical meaning is unchanged.

## Old

The affected consecutive field declarations, verbatim from the quarantine archive:

```lean
  rightAdjoint :
    (lowerStar Λ i).mapDerivedCategory ⊣
      (formalClosedSupport Λ i j).rightDerivedFunctor
  rightAdjoint_eq :
    rightAdjoint = ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
  fiber :
    ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
        (lowerStar Λ j).rightDerivedFunctor ⟶
        ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
          (lowerStar Λ i).mapDerivedCategory) ⋙
          shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
      ∀ K : DerivedCategory (FormalSupportModules Λ X),
        Triangle.mk (rightAdjoint.counit.app K)
          (((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction).unit.app
            K)
          (δ.app K) ∈
          Pretriangulated.distinguishedTriangles
```

## New

```lean
  rightAdjoint :
    letI := ordinaryAdjunction.leftAdjoint_preservesColimits
    (lowerStar Λ i).mapDerivedCategory ⊣
      (formalClosedSupport Λ i j).rightDerivedFunctor
  rightAdjoint_eq :
    letI := ordinaryAdjunction.leftAdjoint_preservesColimits
    rightAdjoint = ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
  fiber :
    letI := ordinaryAdjunction.leftAdjoint_preservesColimits
    ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
        (lowerStar Λ j).rightDerivedFunctor ⟶
        ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
          (lowerStar Λ i).mapDerivedCategory) ⋙
          shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
      ∀ K : DerivedCategory (FormalSupportModules Λ X),
        Triangle.mk (rightAdjoint.counit.app K)
          (((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction).unit.app
            K)
          (δ.app K) ∈
          Pretriangulated.distinguishedTriangles
```

## Users

`tools/downstream.py Sheaf.Paper.FormalClosedSupport --uses FormalClosedSupportAssertions`
reports `unknown module(s)` because the live source is quarantined; with `--allow-missing`,
it reports zero live users and cannot see the archive. The following table
instead conservatively lists the complete transitive import closure computed over live
and quarantined Lean sources, preferring live sources. Eight direct importers are
ClosedAdjointConstructibleYoneda, ClosedSupportConstructible, FormalClosedSupportII,
FormalClosedSupportIILimits, IntegralStratumExtBound, RationalClosedSupportConstructible,
UniformConstructibleExtIntegral, and UniformConstructibleExtTorsion (all under Sheaf.Paper).
Only ClosedAdjointConstructibleYoneda and FormalClosedSupportIILimits project the affected
adjunction; their existing expressions use the same adjunction with the exactness instance
now derived from the stored ordinary adjunction. The other declaration uses concern
unchanged sections or unchanged functors. No consumer requires a mathematical adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Public mathematical interface preserved; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | no current local claim | Uses the derived-adjunction projection; exactness proof is now supplied internally. |
| Sheaf.Paper.ClosedSupportConstructible | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteTorStability | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteWindow | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | no current local claim | Uses the derived-adjunction projection; exactness proof is now supplied internally. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.RestrictionLocal | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.SfBidualityClass | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Paper.VerdierExchange | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Targets.PoincareUncurry | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | no current local claim | Public mathematical interface preserved; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Basic | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.Statement | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | no current local claim | Public mathematical interface preserved; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | no current local claim | Public mathematical interface preserved; no adaptation. |

## Status

landed 20261021T165808-L-2246816 2026-10-21 (merge of deliver/B8/Sheaf.Paper.FormalClosedSupport)
