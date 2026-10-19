# AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap

## Reason

Move the existing pullback-square isomorphism and canonical mate into a shared module so
that the bounded-below comparison and separate truncation estimates can be stated without
importing the theorem that combines them. The definitions and their fully qualified names
are unchanged. The original module publicly imports the shared module and continues to
export both definitions. The new naturality theorem is proved from homEquiv naturality,
the pullback-square naturality and the derived etale counit; it introduces no hole.

## Old

In `Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison`:

```lean
/-- Apply the exact inverse images termwise and localize the specified comparison square.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md; the inverse-image
comparison is sk-thm-pe-direct-image-comparison
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImagePullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)

/-- The specified unbounded comparison: transpose the pullback-square identification
followed by the etale derived counit under the pro-etale derived adjunction.
All direct images are total right derived functors on K-injective resolutions.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md, displayed mate
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImageComparisonMap
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) :=
  ((ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _)
    ((unboundedDirectImagePullbackIso A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.counit.app K))
```

## New

The following declarations now occur in
`Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap`:

```lean
/-- Apply the exact inverse images termwise and localize the specified comparison square.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md; the inverse-image
comparison is sk-thm-pe-direct-image-comparison
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImagePullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)

/-- The specified unbounded comparison: transpose the pullback-square identification
followed by the etale derived counit under the pro-etale derived adjunction.
All direct images are total right derived functors on K-injective resolutions.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md, displayed mate
(blueprint: lem-sfb-unbounded-direct-image-comparison). -/
noncomputable def unboundedDirectImageComparisonMap
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) :=
  ((ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _)
    ((unboundedDirectImagePullbackIso A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.counit.app K))
```

The old module has `public import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap`.
Thus every previously exported name has the same signature, visibility and defining value.
No target's meaning changes. No existing consumer needs adaptation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | K8 | Reexports unchanged definitions; proof uses naturality |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | N4 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteComparisonLocalizing | V7 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.MateOpenRestriction | U2 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.RationalRestrictionGlue | R9 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.RestrictionLocal | R3 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.FiniteCompactProetale | A2 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | Unchanged public signatures and definitions; no adaptation |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.Statement | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.TraceFormula.Statement | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged public signatures and definitions; no adaptation |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged public signatures and definitions; no adaptation |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap | K8 (new) | Shared construction or strict subargument |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow | K8 (new) | Shared construction or strict subargument |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | K8 (new) | Shared construction or strict subargument |

A current source import scan found 228 transitive importers, all listed above.
The earlier downstream.py scan with --uses completed and found 205 transitive importers;
its only textual users of the map were the item and Sheaf.Paper.FiniteComparisonLocalizing.
The three unchanged direct consumers compiled against the sandbox (8.0 s, 3.6 s, 10.8 s).
No existing consumer is edited; both definitions retain their signatures and defining values.
No dependency or cache tool was changed.

## Status

landed 20261019T112453-L-3943137 2026-10-19 (merge of deliver/K8/Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison)
