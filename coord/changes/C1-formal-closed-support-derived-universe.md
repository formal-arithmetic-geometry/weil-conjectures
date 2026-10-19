# formal_closed_support_adjunction

## Reason

The theorem hardcodes `HasDerivedCategory.{u + 2}` although its support constructions
and localization assertion work in any chosen derived-category model. The item uses
the existing Grothendieck models at Hom universe `u + 1`. Applying the original theorem
fails to synthesize `HasDerivedCategory.{u + 2} (FormalSupportModules Λ X)`.
Make the model universe an independent parameter `w`; the old specialization remains
available. No target or definition changes, and no mathematical support assertion changes.
The module is unclaimed. The required downstream declaration-name search found no caller
outside the theorem's own declaration; the new caller is the item. Direct independent
inspection of the source import graph confirms the listed import consumers require
no adaptations. All their statements retain exactly their previous meaning.

## Old

Universe declaration: `universe u`.

```lean
theorem formal_closed_support_adjunction
    {X Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    [HasDerivedCategory.{u + 2} (FormalSupportModules Λ X)]
    [HasDerivedCategory.{u + 2} (FormalSupportModules Λ Z)]
    [HasDerivedCategory.{u + 2} (FormalSupportModules Λ V)] :
    IsIso (formalSupportKernelComparison Λ i j) ∧
    PreservesFiniteLimits (formalClosedSupport Λ i j) ∧
    ∃ a : lowerStar Λ i ⊣ formalClosedSupport Λ i j,
      (∀ M : FormalSupportModules Λ X,
        (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
          (formalSupportKernelInclusion Λ j).app M) ∧
      (∀ (I : FormalSupportModules Λ X) [Injective I],
        Epi ((formalSupportPullbackAdjunction Λ j).unit.app I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        CochainComplex.IsKInjective
          (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        IsIso ((formalClosedSupport Λ i j).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ∧
      (∀ (A : CochainComplex (FormalSupportModules Λ Z) ℤ)
        (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        ∃ e : CochainComplex.HomComplex
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
          CochainComplex.HomComplex A
            (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
          ∀ (n : ℤ) (f : CochainComplex.HomComplex.Cochain
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
            (p q : ℤ) (hpq : p + n = q),
            (((e.hom.f n).hom f).v p q hpq) =
              a.homEquiv (A.X p) (I.X q) (f.v p q hpq)) ∧
      Exists fun [hclosed : PreservesFiniteColimits (lowerStar Λ i)] ↦
        ∃ (b : (lowerStar Λ i).mapDerivedCategory ⊣
            (formalClosedSupport Λ i j).rightDerivedFunctor)
          (c : (formalSupportPullback Λ j).mapDerivedCategory ⊣
            (lowerStar Λ j).rightDerivedFunctor),
          ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
              (lowerStar Λ j).rightDerivedFunctor ⟶
            (formalClosedSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory ⋙
                shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
            b = a.mapDerivedCategoryRightDerivedAdjunction ∧
            c = (formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction ∧
            (∀ K : DerivedCategory (FormalSupportModules Λ X),
              Triangle.mk (b.counit.app K) (c.unit.app K) (δ.app K) ∈ distTriang _) ∧
            (∀ (K F : DerivedCategory (FormalSupportModules Λ X)) (s : F ⟶ K)
              (t : (lowerStar Λ j).rightDerivedFunctor.obj
                ((formalSupportPullback Λ j).mapDerivedCategory.obj K) ⟶ F⟦(1 : ℤ)⟧),
              Triangle.mk s (c.unit.app K) t ∈ distTriang _ →
              Nonempty ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K ≅
                (formalSupportPullback Λ i).mapDerivedCategory.obj F))
```

## New

Universe declaration: `universe u w`.

```lean
theorem formal_closed_support_adjunction
    {X Z V : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    [HasDerivedCategory.{w} (FormalSupportModules Λ X)]
    [HasDerivedCategory.{w} (FormalSupportModules Λ Z)]
    [HasDerivedCategory.{w} (FormalSupportModules Λ V)] :
    IsIso (formalSupportKernelComparison Λ i j) ∧
    PreservesFiniteLimits (formalClosedSupport Λ i j) ∧
    ∃ a : lowerStar Λ i ⊣ formalClosedSupport Λ i j,
      (∀ M : FormalSupportModules Λ X,
        (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
          (formalSupportKernelInclusion Λ j).app M) ∧
      (∀ (I : FormalSupportModules Λ X) [Injective I],
        Epi ((formalSupportPullbackAdjunction Λ j).unit.app I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        CochainComplex.IsKInjective
          (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        IsIso ((formalClosedSupport Λ i j).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ∧
      (∀ (A : CochainComplex (FormalSupportModules Λ Z) ℤ)
        (I : CochainComplex (FormalSupportModules Λ X) ℤ) [I.IsKInjective],
        ∃ e : CochainComplex.HomComplex
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
          CochainComplex.HomComplex A
            (((formalClosedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
          ∀ (n : ℤ) (f : CochainComplex.HomComplex.Cochain
            (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
            (p q : ℤ) (hpq : p + n = q),
            (((e.hom.f n).hom f).v p q hpq) =
              a.homEquiv (A.X p) (I.X q) (f.v p q hpq)) ∧
      Exists fun [hclosed : PreservesFiniteColimits (lowerStar Λ i)] ↦
        ∃ (b : (lowerStar Λ i).mapDerivedCategory ⊣
            (formalClosedSupport Λ i j).rightDerivedFunctor)
          (c : (formalSupportPullback Λ j).mapDerivedCategory ⊣
            (lowerStar Λ j).rightDerivedFunctor),
          ∃ δ : (formalSupportPullback Λ j).mapDerivedCategory ⋙
              (lowerStar Λ j).rightDerivedFunctor ⟶
            (formalClosedSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory ⋙
                shiftFunctor (DerivedCategory (FormalSupportModules Λ X)) (1 : ℤ),
            b = a.mapDerivedCategoryRightDerivedAdjunction ∧
            c = (formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction ∧
            (∀ K : DerivedCategory (FormalSupportModules Λ X),
              Triangle.mk (b.counit.app K) (c.unit.app K) (δ.app K) ∈ distTriang _) ∧
            (∀ (K F : DerivedCategory (FormalSupportModules Λ X)) (s : F ⟶ K)
              (t : (lowerStar Λ j).rightDerivedFunctor.obj
                ((formalSupportPullback Λ j).mapDerivedCategory.obj K) ⟶ F⟦(1 : ℤ)⟧),
              Triangle.mk s (c.unit.app K) t ∈ distTriang _ →
              Nonempty ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K ≅
                (formalSupportPullback Λ i).mapDerivedCategory.obj F))
```

## Users

Import consumers from `tools/downstream.py`, independently checked against source imports.
Only the item newly calls this theorem. Holders are recorded at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction | unclaimed | Generalizes only the theorem model universe; no definition changes. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ConstructibleCompactness | U7 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteWindow | W5 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteWindowBounded | C1 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FormalClosedSupport | Q9 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FormalClosedSupportII | M2 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FormalClosedSupportIILimits | W6 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IndHeartIIVanishing | E9 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralConstructibleExt | J9 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.MateOpenRestriction | D7 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RationalClosedSupportConstructible | C1 | New caller at Hom universe u+1; original statement proved. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RestrictionLocal | R3 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.SmoothTrace | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.UniformConstructibleExt | X9 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.VerdierExchange | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.WeilOne | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | No adaptation: does not use the changed theorem. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No adaptation: does not use the changed theorem. |
| TargetsCheck | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.Statement | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No adaptation: does not use the changed theorem. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No adaptation: does not use the changed theorem. |
| Weil.Solution | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No adaptation: does not use the changed theorem. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No adaptation: does not use the changed theorem. |

## Status

landed 20261019T005259-L-2747459 2026-10-19 (merge of deliver/C1/Sheaf.Paper.RationalClosedSupportConstructible)
