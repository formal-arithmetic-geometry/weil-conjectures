# CategoryTheory.constantRealizationReflectsIsomorphism

## Reason

Repair of returned delivery ef3ed2071: the landing hole census interpreted the component
`sorry` in the file option `warn.sorry` as an unattributed proof hole. Remove the unnecessary
warning suppression. The static interface check classifies removal of a file-level command
as potentially visible, so this record documents its scope. Lean options apply to elaboration
of this file and are not exported as options to importing modules. No mathematical statement,
definition, universe, visibility, or public import changes. The retained proof closes the
original named theorem using exact derived homology comparisons and kernel/cokernel detection.

## Old

The file-level options and theorem signature were:

```lean
set_option autoImplicit false
set_option warn.sorry false

theorem constantRealizationReflectsIsomorphism
    {X : Scheme.{u}} (U : X.ProEt) (R : Type (u + 1)) [CommRing R]
    [Nonempty U.left]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u + 1}
        ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u + 1}
        (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of R)).over U))] :
    (∀ i : ℤ,
      Nonempty ((siteDerivedConstantModuleFunctor.{u + 1, u, wR, wS} (Scheme.ProEt.topology X) R ⋙
          ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, wS, wU}
            ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u + 1}
              (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
                (RingCat.of R)).over U)) i) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i ⋙
          siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R ⋙
          SheafOfModules.overFunctor
            ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U))) ∧
      (∀ {C D : DerivedCategory (ModuleCat.{u + 1} R)} (f : C ⟶ D),
        IsIso ((ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, wS, wU}
          ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U).map
          ((siteDerivedConstantModuleFunctor.{u + 1, u, wR, wS}
            (Scheme.ProEt.topology X) R).map f)) →
          IsIso f)
```

The theorem proof was `by sorry` in the current repository.

## New

The file-level options and theorem signature are:

```lean
set_option autoImplicit false

theorem constantRealizationReflectsIsomorphism
    {X : Scheme.{u}} (U : X.ProEt) (R : Type (u + 1)) [CommRing R]
    [Nonempty U.left]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u + 1}
        ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u + 1}
        (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of R)).over U))] :
    (∀ i : ℤ,
      Nonempty ((siteDerivedConstantModuleFunctor.{u + 1, u, wR, wS} (Scheme.ProEt.topology X) R ⋙
          ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, wS, wU}
            ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u + 1}
              (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
                (RingCat.of R)).over U)) i) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i ⋙
          siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R ⋙
          SheafOfModules.overFunctor
            ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U))) ∧
      (∀ {C D : DerivedCategory (ModuleCat.{u + 1} R)} (f : C ⟶ D),
        IsIso ((ringedDerivedRestrictionGeneral.{u + 1, u, u + 1, u + 1, wS, wU}
          ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of R)) U).map
          ((siteDerivedConstantModuleFunctor.{u + 1, u, wR, wS}
            (Scheme.ProEt.topology X) R).map f)) →
          IsIso f)
```

The theorem now has a complete proof, with zero local holes. The proof-only commutative
constant-functor import is removed; the exact-derived-functor comparison import is added.
Neither proof import is public. No declaration is added or removed.

## Users

`tools/downstream.py Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism
--uses CategoryTheory.constantRealizationReflectsIsomorphism` reported 234 transitive
importers and only the item itself as a textual reference to the declaration. The list
below includes every transitive importer, with claim holders at the time of this check.
The theorem signature was compared verbatim with the current repository. Since the only
command change removes a file-local warning setting, every downstream statement retains
its original meaning. No dependent module needs adaptation, and no target review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism | E9 | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | Signature and meaning unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicResidueLissePerfectLift | V6 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AdicStratifiedPerfect | P5 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | H5 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | F4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | V4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | H7 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | D4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | S4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | D7 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | R3 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.WContractibleConstantReductionsML | Z6 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Signature and meaning unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Signature and meaning unchanged; no adaptation. |
| TargetsCheck | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Signature and meaning unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Signature and meaning unchanged; no adaptation. |

## Status

landed 20261019T002537-L-2150787 2026-10-19 (merge of deliver/E9/Sheaf.CategoryTheory.ConstantRealizationReflectsIsomorphism)
