# AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived

## Reason

Restore the complete module from the quarantine path recorded in coord/rework.tsv.
The archived source has zero holes, but compiling it against the current library fails
at the statement's derived triangle with two errors:
`failed to synthesize instance of type class PreservesFiniteColimits (i)_*⟦Λ⟧`.
The quantified adjunction `adj : lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j`
already proves colimit preservation. Bind that proof as a local instance immediately
after the existential adjunction, using `adj.leftAdjoint_preservesColimits`.

This adds no hypothesis, existential field, or mathematical conclusion. After reduction
of the let, the result has the original conjunction shape. The derived functors and
adjunction depend on exactness only through Prop-valued proof arguments; proof
irrelevance identifies this choice with any other proof of the same exactness.
All public binders, universes, names, visibilities and public imports are preserved.
No definition or target statement changes, so no target semantic review is reopened.

Remove the redundant private import Mathlib.CategoryTheory.Triangulated.Triangulated;
its used APIs are already publicly available through the retained support dependency.
All four private, completely proved helper declarations and the theorem proof remain
identical to the archive. This is a zero-hole restoration and elaboration repair.

## Old

The live item is absent; the preserved quarantine source has the following signature.

```lean
theorem formal_closed_support_derived
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range j = (Set.range i)ᶜ) :
    ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
      ∃ adj : lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j,
        (∀ (A : CochainComplex (pulledBackModuleObjects Λ Z) ℤ)
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective],
          ∃ e : CochainComplex.HomComplex
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
            CochainComplex.HomComplex A
              (((closedModuleSectionsWithSupport Λ i j).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I),
            ∀ (n : ℤ) (a : CochainComplex.HomComplex.Cochain
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
              (p q : ℤ) (hpq : p + n = q),
              (e.hom.f n a) ⟨p, q, hpq⟩ =
                adj.homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩)) ∧
        (∀ (I : pulledBackModuleObjects Λ X) [Injective I],
          Epi ((upperStarLowerStarAdjunction Λ j).unit.app I)) ∧
        (∃ δ : (upperStar Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
            ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory) ⋙
                shiftFunctor (DerivedCategory (pulledBackModuleObjects Λ X)) (1 : ℤ),
          ∀ K : DerivedCategory (pulledBackModuleObjects Λ X),
            Triangle.mk (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
              ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
                K)
              (δ.app K) ∈ Pretriangulated.distinguishedTriangles) ∧
        (∀ (K : DerivedCategory (pulledBackModuleObjects Λ X))
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective]
          (_e : K ≅ DerivedCategory.Q.obj I),
          Nonempty ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor.obj K ≅
            (upperStar Λ i).mapDerivedCategory.obj
              (DerivedCategory.Q.obj
                ((shiftFunctor (CochainComplex (pulledBackModuleObjects Λ X) ℤ) (-1 : ℤ)).obj
                  (CochainComplex.mappingCone
                    ((NatTrans.mapHomologicalComplex (upperStarLowerStarAdjunction Λ j).unit
                      (ComplexShape.up ℤ)).app I))))))
```

## New

```lean
theorem formal_closed_support_derived
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range j = (Set.range i)ᶜ) :
    ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
      ∃ adj : lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j,
        letI : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
          adj.leftAdjoint_preservesColimits
        (∀ (A : CochainComplex (pulledBackModuleObjects Λ Z) ℤ)
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective],
          ∃ e : CochainComplex.HomComplex
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
            CochainComplex.HomComplex A
              (((closedModuleSectionsWithSupport Λ i j).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I),
            ∀ (n : ℤ) (a : CochainComplex.HomComplex.Cochain
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
              (p q : ℤ) (hpq : p + n = q),
              (e.hom.f n a) ⟨p, q, hpq⟩ =
                adj.homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩)) ∧
        (∀ (I : pulledBackModuleObjects Λ X) [Injective I],
          Epi ((upperStarLowerStarAdjunction Λ j).unit.app I)) ∧
        (∃ δ : (upperStar Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
            ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory) ⋙
                shiftFunctor (DerivedCategory (pulledBackModuleObjects Λ X)) (1 : ℤ),
          ∀ K : DerivedCategory (pulledBackModuleObjects Λ X),
            Triangle.mk (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
              ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
                K)
              (δ.app K) ∈ Pretriangulated.distinguishedTriangles) ∧
        (∀ (K : DerivedCategory (pulledBackModuleObjects Λ X))
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective]
          (_e : K ≅ DerivedCategory.Q.obj I),
          Nonempty ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor.obj K ≅
            (upperStar Λ i).mapDerivedCategory.obj
              (DerivedCategory.Q.obj
                ((shiftFunctor (CochainComplex (pulledBackModuleObjects Λ X) ℤ) (-1 : ℤ)).obj
                  (CochainComplex.mappingCone
                    ((NatTrans.mapHomologicalComplex (upperStarLowerStarAdjunction Λ j).unit
                      (ComplexShape.up ℤ)).app I))))))
```

## Users

The stock `tools/downstream.py Sheaf.Paper.FormalClosedSupportDerived --uses
formal_closed_support_derived` query reports unknown module because its source is
quarantined. The inventory below conservatively scans all live and quarantined
Sheaf/WeilConjectures sources, with live sources taking precedence. It finds
185 transitive consumers. Claims were read from coord/claims at preparation time.

The four direct importers are Sheaf.Paper.FormalClosedSupport,
Sheaf.Paper.IntegralStratumHomFormula, Sheaf.SixFunctors.IntegralExtHomContinuity,
and Sheaf.SixFunctors.IntegralRestrictionClosed. All four are currently quarantined.
Only IntegralRestrictionClosed directly uses the theorem: its existing
`obtain ⟨hAdd, adj, _, _, ⟨δ, hδ⟩, _⟩` still has exactly the same result shape,
since the added instance is a let, not an extra conjunction or existential.
The public import closure is unchanged. No consumer requires adaptation; none is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same proposition; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same proposition; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same proposition; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same proposition; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Same proposition; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | C1 | Same proposition; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same proposition; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same proposition; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same proposition; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Same proposition; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same proposition; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same proposition; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same proposition; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same proposition; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same proposition; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same proposition; no adaptation. |

## Status

landed 20261021T021003-L-2687808 2026-10-21 (merge of deliver/C1/Sheaf.Paper.FormalClosedSupportDerived)
