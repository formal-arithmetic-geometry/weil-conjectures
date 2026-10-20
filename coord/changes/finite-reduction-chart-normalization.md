# WeilConjectures.PurityFiniteSetting.FiniteReductionFixedChartNormalized

## Reason

The original existential factor presentation makes the completed fixed-chart proof exceed
60 seconds in kernel checking. Each factor individually checks in under 15 seconds.
Cache the ordered composite at an abstract coefficient ring, and normalize by its exact
heterogeneous equality. The private proved lemma
`finiteReductionChartComposite_normalized` establishes equivalence with the original
three-factor existential presentation at an abstract ring, including the existential middle
root chart. No maps, hypotheses, endpoints, or choice conditions change.
The three-factor composite is actual data constructed from the existing isomorphisms.

## Old

```lean
def FiniteReductionFixedChartNormalized (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (a : (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧) : Prop :=
  let S := P.FiniteReductionFixedChartStage X d M
  ∃ i₀ : S 0 ≅ S 1, ∃ i₁ : S 1 ≅ S 2, ∃ i₂ : S 2 ≅ S 3,
    HEq i₀ (P.smoothPurityReassociation X d M) ∧
    (∃ b : P.diagonalTwist X d ≅
        ((𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))))⟦2 * (d : ℤ)⟧),
      HEq b (P.finiteReductionPowerTrivialization X ζ hζ d ≪≫
        (shiftFunctor _ (2 * (d : ℤ))).mapIso
          (finiteReductionComparisonUnitChart P.Coefficient X)) ∧
      HEq i₁ (((smoothPurityTensor P.Coefficient X).obj M).mapIso b)) ∧
    HEq i₂ (finiteReductionTensorUnit
      (ModuleCat.{u + 1} P.Coefficient) X M (2 * (d : ℤ))) ∧
    HEq a (i₀ ≪≫ i₁ ≪≫ i₂)
```

## New

```lean
def FiniteReductionFixedChartNormalized (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    (d : ℕ) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (a : (P.compositionTwistShift X d).obj M ≅ M⟦2 * (d : ℤ)⟧) : Prop :=
  HEq a (finiteReductionChartComposite P.Coefficient X M (P.diagonalTwist X d) (2 * (d : ℤ))
    (P.finiteReductionPowerTrivialization X ζ hζ d ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        (finiteReductionComparisonUnitChart P.Coefficient X)))
```

`finiteReductionChartComposite` constructs the reassociation, tensor image of the given
root-power/unit chart, and native tensor-unit comparison in that order. Its generic
factor-normalization equivalence is proved in this module, without additional assumptions.

## Users

`tools/downstream.py Sheaf.Paper.FiniteReductionRootCharts --uses
FiniteReductionFixedChartNormalized` reports 156 transitive importers and only the following
textual user. A full `rg` over both library roots confirms that no other module names the
normalization predicate. Every downstream statement retains its meaning because the new
predicate is equivalent to the old one and selects exactly the same unique isomorphism.
The target statements are unchanged; the representation change lies in their dependency
closure and is submitted for independent definition review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Equivalent normalization; completed proof. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.PurityChernClasses | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.WeilOne | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not queried (untouched) | No reference to the predicate; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried (untouched) | No reference to the predicate; no adaptation. |
| TargetsCheck | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.Statement | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried (untouched) | No reference to the predicate; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | not queried (untouched) | No reference to the predicate; no adaptation. |

No other module needs adaptation. Existing public signatures and visibility are preserved.

## Status

landed 20261020T051152-L-1584661 2026-10-20 (merge of deliver/D8/Sheaf.Paper.FiniteReductionRootCharts)
