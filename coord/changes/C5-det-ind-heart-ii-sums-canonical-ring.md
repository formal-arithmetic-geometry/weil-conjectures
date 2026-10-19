# AlgebraicGeometry.ProEtale.det_ind_heart_ii_sums

## Reason

The original signature takes an abelian sheaf Λ with an arbitrary MonObj instance.
Its equality hΛ identifies only the underlying abelian sheaf with the field coefficient
sheaf; it does not identify its multiplication or unit. Consequently it does not specify
the field coefficient ring required by the blueprint or by constructible Ext continuity.
Bind the condensed ring R itself and use its canonical underlying ring object, exactly
as in constructible_sheaf_ext_continuity. The Noetherian scope, constructibility, all
integer degrees, ind-constructible family, cofan and canonical comparison stay the same.
This corrects an auxiliary theorem interface; no target signature or definition changes.

## Old

```lean
theorem det_ind_heart_ii_sums
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Λ = Profinite.continuousMapRingObj E ∨
      Λ = Profinite.padicAlgClRingObj ℓ)
    (C : CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (hC : IsConstantModelConstructible Λ X C)
    (q : ℤ) (S : Type (u + 1))
    (B : S → CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (hB : ∀ s : S, ObjectProperty.ind
      (IsConstantModelConstructible Λ X) (B s))
    (c : Cofan B) (hc : IsColimit c) :
    Function.Bijective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun s : S ↦
        Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj C)
          ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor _ 0).map (c.inj s)))) :
        (⨁ s : S,
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj (B s)))) →+
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt)))
```

## New

```lean
theorem det_ind_heart_ii_sums
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj R)]
    (hR : R = Profinite.padicSubfieldCondensedRing ℓ E ∨
      R = Profinite.padicAlgClCondensedRing ℓ)
    (C : CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj R) X C)
    (q : ℤ) (S : Type (u + 1))
    (B : S → CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj R) X))
    (hB : ∀ s : S, ObjectProperty.ind
      (IsConstantModelConstructible (coefficientHeartRingObj R) X) (B s))
    (c : Cofan B) (hc : IsColimit c) :
    Function.Bijective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun s : S ↦
        Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj C)
          ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor _ 0).map (c.inj s)))) :
        (⨁ s : S,
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj (B s)))) →+
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt)))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DetIndHeartIISums | C5 | Owning theorem: coefficient ring fixed canonically. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Direct proof import only; no application; statement unchanged. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.MateOpenRestriction | D7 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.RestrictionLocal | R3 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.SmoothTrace | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.VerdierExchange | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.WeilOne | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1 | Transitive importer only; no application; signatures unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Transitive importer only; no application; signatures unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive importer only; no application; signatures unchanged. |
| TargetsCheck | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.Statement | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive importer only; no application; signatures unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive importer only; no application; signatures unchanged. |

The required downstream.py audit completed successfully: 204 transitive importers;
its only declaration-use hit is the owning module. An independent exact import-source
scan using leanindex.imports_of gives 204 transitive importers, all inventoried
above, including the top-level library roots. Whole-library name and import searches
confirm one direct importer, ConstructibleCompactnessBounded, and no existing
application. The unchanged direct importer compiled against this interface. No
consumer needs adaptation. Holdings above are a source snapshot; no module held
by another group is edited.

## Status

landed 20261019T002515-L-2143960 2026-10-19 (merge of deliver/C5/Sheaf.Paper.DetIndHeartIISums)
