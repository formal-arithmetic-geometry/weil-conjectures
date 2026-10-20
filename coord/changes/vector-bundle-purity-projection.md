# AlgebraicGeometry.Etale.vectorBundlePurityProjectionMap

## Reason

Use the existing canonical coefficient-first compact-support projection wrapper instead
of elaborating its three-factor expansion again at concrete ModuleCat coefficients.
Comparing the two expanded monoidal-instance terms in the purity proof repeatedly exceeded
the 60-second compiler limit. The wrapper version compiles the complete parent; the final import-order packet check took 54.8 seconds for the parent.
Both constructions use the same chosen Nagata compactification, signed tensor symmetries,
and canonical projection arrow; the mathematical map is unchanged. The local high-priority
symmetric-to-braided instance selects the canonical symmetry while elaborating this file.
The new public import supplies the definition used by this public construction.

## Old

```lean
def vectorBundlePurityProjectionMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (vectorIntegrationSource A N hA S d M) ⟶
      (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M K) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app K).app _ ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A)
      (vectorBundlePurityCompactification S d M)).app
        (vectorIntegrationCoefficient A N hA S d M)).app K ≫
    (vectorBundlePurityLower A S d M).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.scheme S d M)).hom.app
          (vectorIntegrationCoefficient A N hA S d M)).app _)
```

## New

```lean
def vectorBundlePurityProjectionMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (vectorIntegrationSource A N hA S d M) ⟶
      (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M K) :=
  letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
    (vectorIntegration_geometry S d M).2.1
  compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
    (vectorIntegrationCoefficient A N hA S d M)
```

## Users

The current downstream check lists 219 import descendants and two textual
users (including this module). All are listed below. Indirect consumers retain the same
public interfaces; the canonical projection and its mathematical meaning are unchanged.
The two textual users require no adaptation beyond this module’s proof.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.ChernFlagFormula | G4 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteRingSectionDeformation | G9 | Map occurs only in hp in bundleOrientation_purity; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.LocalizedTopChern | E5 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.PurAdicReconstruction | H8 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.PurityDncComparisons | G3 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.SfBidualityClass | C6 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.SmoothPurityMap | R2 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.SmoothTrace | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.VectorBundlePurity | S1 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.VerdierExchange | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.WeilFourierInversion | J6 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.WeilOne | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SixFunctors.RationalVerdier | V4 | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| Sheaf.Targets.VectorBundlePurity | F6 | Canonical wrapper replaces its identical expansion; proof updated. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| TargetsCheck | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.Statement | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No occurrence of the map; unchanged public interfaces and statement meaning. |

## Status

landed 20261020T051251-L-1615201 2026-10-20 (merge of deliver/F6/Sheaf.Targets.VectorBundlePurity)
