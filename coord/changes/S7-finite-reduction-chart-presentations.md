# FiniteReductionChartCalculus tensor presentation and imports

## Reason

The proofs now compare the published derived tensors with the native curried tensor at an abstract coefficient category, then transport only the endpoint type. This avoids expensive kernel comparison of the concrete module-category instance. The two existing generic constructions receive explicit annotations for their previously inferred result types; their construction terms and binders are unchanged. Redundant public imports are removed.

## Old

```lean
public import Sheaf.Paper.SmoothTrace
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
```

```lean
def finiteReductionUnitStepGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (U : _root_.DerivedCategory C) (z : U ≅ 𝟙_ (_root_.DerivedCategory C)) (n : ℕ) :=
  _root_.DerivedCategory.shiftTensorShiftIso C U U (2 * (n : ℤ)) 2 ≪≫
    (shiftFunctor _ (2 * (n : ℤ) + 2)).mapIso
      (((curriedTensor (_root_.DerivedCategory C)).obj U).mapIso z ≪≫ ρ_ U) ≪≫
    (eqToIso (congrArg (fun a : ℤ ↦ shiftFunctor (_root_.DerivedCategory C) a)
      (finiteReductionPowerShift n))).app U
```

```lean
def finiteReductionTensorUnitGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (M : _root_.DerivedCategory C) (r : ℤ) :=
  letI := _root_.DerivedCategory.commShiftTensorLeft C M
  (((curriedTensor (_root_.DerivedCategory C)).obj M).commShiftIso r).app
      (𝟙_ (_root_.DerivedCategory C)) ≪≫
    (shiftFunctor _ r).mapIso (ρ_ M)
```

## New

The listed imports are removed; the retained public import is `Sheaf.Paper.PurityCompositionCoherence`. The annotated definitions are:

```lean
def finiteReductionUnitStepGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (U : _root_.DerivedCategory C) (z : U ≅ 𝟙_ (_root_.DerivedCategory C)) (n : ℕ) :
    ((curriedTensor (_root_.DerivedCategory C)).obj (U⟦2 * (n : ℤ)⟧)).obj (U⟦(2 : ℤ)⟧) ≅
      U⟦2 * ((n + 1 : ℕ) : ℤ)⟧ :=
  _root_.DerivedCategory.shiftTensorShiftIso C U U (2 * (n : ℤ)) 2 ≪≫
    (shiftFunctor _ (2 * (n : ℤ) + 2)).mapIso
      (((curriedTensor (_root_.DerivedCategory C)).obj U).mapIso z ≪≫ ρ_ U) ≪≫
    (eqToIso (congrArg (fun a : ℤ ↦ shiftFunctor (_root_.DerivedCategory C) a)
      (finiteReductionPowerShift n))).app U
```

```lean
def finiteReductionTensorUnitGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (M : _root_.DerivedCategory C) (r : ℤ) :
    ((curriedTensor (_root_.DerivedCategory C)).obj M).obj
      ((𝟙_ (_root_.DerivedCategory C))⟦r⟧) ≅ M⟦r⟧ :=
  letI := _root_.DerivedCategory.commShiftTensorLeft C M
  (((curriedTensor (_root_.DerivedCategory C)).obj M).commShiftIso r).app
      (𝟙_ (_root_.DerivedCategory C)) ≪≫
    (shiftFunctor _ r).mapIso (ρ_ M)
```

The annotations state exactly the isomorphism endpoints of the unchanged native tensor-shift/unitor composites. No target, theorem statement, construction term, instance registration, visibility or file-level option changes.

## Users

`tools/downstream.py Sheaf.Paper.FiniteReductionChartCalculus --uses finiteReductionUnitStepGeneric finiteReductionTensorUnitGeneric` lists 157 transitive consumers. Neither annotated name occurs in any consumer. The sole direct importer, `Sheaf.Paper.FiniteReductionRootCharts`, already explicitly imports every removed module. Thus all consumers retain these dependencies through that importer. No consumer requires adaptation, and no consumer is delivered. Holder queries are unnecessary for unchanged consumers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.DeligneLaumon.Reduction.Composition | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.AdicPurityExceptionalReduction | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.AdicPurityFiniteTensor | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.AdicPurityObjects | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.AdicPurityRootComparisons | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.AdicPuritySourceReduction | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.AdicPurityTwistReduction | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.ArithmeticRoots | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.ChernFlagFormula | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.CurveIntermediateExtension | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.DualizingObjectPurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.ExtensionByZeroPunctual | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FiniteReductionAffineOrientation | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FiniteReductionComparisons | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FiniteReductionOfPurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FiniteReductionRootCharts | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FlagLocalComparison | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FlagPullbackInjective | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.FourierTraceFormula | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.LocalizedFlagProduct | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.LocalizedTopChern | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.ProjectiveBundleFormula | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.PurAdicReconstruction | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.PurityChernClasses | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.RationalPurityPresentation | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.SupportedProjectionSplitting | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.TwistFrobeniusScalar | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.VectorBundleThomClass | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.WeilFourierInversion | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.WeilFourierPlancherel | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.WeilOne | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.Paper.ZlShriekComposition | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| TargetsCheck | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.Statement | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.Curve | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.EulerProduct | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierInversion | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierStalk | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.FourierTrace | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.LFunction | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.RealPurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.VerdierDual | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.Examples | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.LissePurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.Rationality | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |
| WeilConjectures.ZetaFunction.Weights | not queried; not adapted | Same constructions and types; imports retained through RootCharts. |

## Status

landed 20261019T231342-L-577135 2026-10-19 (merge of deliver/S7/Sheaf.Paper.FiniteReductionChartCalculus)
