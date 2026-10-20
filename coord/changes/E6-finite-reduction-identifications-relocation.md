# sfbConstantRingAbIso and sfbFiniteCoefficientPullbackIso

## Reason

The single finite-reduction mate calculation is independent of the integral limit.
Its statement needs the two existing canonical finite constant-sheaf identifications.
Move those definitions verbatim into the new lower module to avoid a circular import.
The original module publicly imports that module, preserving every public name,
signature, universe, visibility and definition body. This is a relocation, not a
change of coefficients or normalization. No target statement changes meaning.

## Old

In Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback:

```lean
def sfbConstantRingAbIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)) ≅
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of A) :=
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  letI : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app A) ≪≫
    (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).app ((forget₂ CommRingCat RingCat).obj A)

def sfbFiniteCoefficientPullbackIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (f)^*[Ab.{u + 1}].obj
        ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (integralCoefficientSheaf l E Y n)) ≅
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (integralCoefficientSheaf l E X n) :=
  (f)^*[Ab.{u + 1}].mapIso
    (sfbConstantRingAbIso Y
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    (constantSheafCompUpperStarIso Ab.{u + 1} f).app
      (AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ≪≫
    (sfbConstantRingAbIso X
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).symm
```

## New

The exact same declarations and bodies above, now in
Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback. The original module has
`public import Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback`.
The public signatures and definition bodies are identical.

## Users

`tools/downstream.py --uses` finds direct textual uses of both definitions only
in the item itself. Its transitive downstream list is recorded below. No consumer
requires an adaptation: the original module re-exports the exact declarations.
No module held by another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | E6 | Definitions relocated verbatim and publicly re-exported; proof now uses the finite lemma. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback | new in this delivery | Owns the two unchanged definitions and one finite-level theorem. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.DeligneLaumon.GenericDualityModel | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.DeligneLaumon.Reduction.Composition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicExceptionalCoherence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicExceptionalComposition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicExceptionalProjection | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicExceptionalScalars | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicPurityFiniteTensor | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicPurityObjects | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicPurityRootComparisons | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicPuritySourceReduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicPurityTwistReduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicSectionClosedSupport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AdmissibleVerdierExchange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AffineSpaceRationalInduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AmbientIndDerivedSums | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ArithmeticRoots | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.BrownExceptionalAdjoint | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.BrownHypothesesGeneration | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CartesianCoefficientTwists | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CartesianCoefficients | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ChernFlagFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ClosedSupportConstructible | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CoefficientHeart | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CoefficientHeartFiltration | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CoefficientHeartGeneration | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CompactificationCoherenceCocycle | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CompactificationLocalizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CompactificationRefinementIdentity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstantExtensionCompactComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstructibleCompactness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstructibleCompactnessBounded | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstructibleExtContinuity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CurveIntermediateExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DerivedTruncationCoproducts | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DetIndHeartIISums | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DiagonalTowerLimit | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DiagonalTowerTrace | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DiagonalTowerTraceLimit | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DiagonalTowerTraceModels | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DiagonalTowerTracePresentations | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DlConstantFieldCharts | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DlConstructibleFibresExact | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.DualizingObjectPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ExtensionByZeroPunctual | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteFreeCompactComposition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteProperLocalizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteReductionChartCalculus | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteReductionComparisons | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteReductionOfPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteReductionRootCharts | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteRegularReductionDualizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteTorStability | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteWindow | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteWindowBounded | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FiniteWindowUnbounded | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FlagLocalComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FlagPullbackInjective | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FormalClosedSupport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FormalClosedSupportII | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FormalClosedSupportIILimits | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.FourierTraceFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IndConstructibleExtensions | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IndConstructibleFilteredColimits | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IndHeartCanonicalPresentation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IndHeartFullFaithfulness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IndHeartIIVanishing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IndHeartKernelsCokernels | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralConstantModelHeart | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralConstructibleCompactness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralConstructibleExt | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralConstructibleHeart | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralCriterionReductions | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralDirectImageTower | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralHeartDualizable | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralHeartLocalModel | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralIndHeartRealization | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralIndLowerTail | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralModels | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralModelsOperations | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralProperBaseChange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralProperDirectSums | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralProperProjectionFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralStratumExtBound | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralStratumHomFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralTensorProduct | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralTensorPullback | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralTwistBaseChange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralTwistDerivedScalar | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralTwistScalarCoherence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.IntegralWindowCoproductComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.InterchangeProperPasting | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.InternalHomDualConstructibleModels | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.KummerAdditivity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.LocalizedFlagProduct | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.LocalizedTopChern | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.MateOpenRestriction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.MiddleExtensionHcZero | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ModelCompactComparisonUnit | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.NonrationalCompositionSeed | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.OpenImmersionLocalizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProjectiveBundleFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperBaseChangeRational | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperExceptionalRestriction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperHeartBound | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperHeartBoundLattice | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperHeartBoundReduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperUnboundedCoproducts | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperUnboundedWindow | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ProperUnboundedWindowIso | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.PurAdicReconstruction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.PurityChernClasses | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.PurityCompositionCoherence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.PurityDiagonalDualizingObject | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.PurityTwistCancellation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.QbarAffineSupportBound | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.QbarMiddleTStructure | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.QbarPerverseSubcategories | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.QbarTwistCommonStage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalClosedSupportConstructible | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalExceptionalRestriction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalPurityPresentation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalRestrictionGlue | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalStalkExact | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RegularImmersionPurityComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.RestrictionLocal | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SfBidualityClass | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SmoothPurityMap | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SmoothTrace | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.StratifiedLatticeRank | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.SupportedProjectionSplitting | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TateTwistLisseLine | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TateTwistSupportCondition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TraceBaseChangeFirst | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TraceBaseChangeSecond | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TwistFrobeniusScalar | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.TwistPreservesFiniteness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.UnboundedBaseChangeExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.UniformConstructibleExt | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.UniformConstructibleExtIntegral | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.UniformConstructibleExtRational | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.UniformConstructibleExtTorsion | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.VaryingRingGraphSummand | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.VectorBundleThomClass | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.VerdierExchange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.WeilFourierInversion | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.WeilFourierPlancherel | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.WeilOne | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.WeilOpenImageDelta | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Paper.ZlShriekComposition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.BrownHypothesesSmall | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.FieldTensor | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.FiniteDualizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.FiniteExceptional | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralDualizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralModelsGenerators | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.IntegralVerdier | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.QbarDualRecollement | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.RationalOperations | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctors.RationalVerdier | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Targets.AffineSpaceRationalLine | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Targets.PoincareUncurry | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.Targets.SmoothPurityQbar | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| TargetsCheck | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.PoincareDuality.Poincare | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.PoincareDuality.Verdier | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Adic.Reduction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.SmoothPurity.Defs | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.Statement | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Basic | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.Basic | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.Main | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.TraceFormula.Statement | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.Curve | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.EulerProduct | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierInversion | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierStalk | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.FourierTrace | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.LFunction | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.LocalizationRational | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.RealPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.VerdierDual | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.Examples | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.LissePurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.Rationality | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; no edit | Exact declarations re-exported; no change of statement or body. |
| WeilConjectures.ZetaFunction.Weights | not queried; no edit | Exact declarations re-exported; no change of statement or body. |

## Status

landed 20261020T051219-L-1596947 2026-10-20 (merge of deliver/E6/Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback)
