# AlgebraicGeometry.ProEtale.supportOpenBaseChangeApp

## Reason

The direct proof of naturality makes kernel conversion expand the composite
base-change mate and inverse-image comparison, and exceeds the single-file limit.
Package their whiskered composite once as `supportOpenBaseChange`, a natural
transformation. Its component is the existing specified map, definitionally equal
to the original expression; its naturality field proves the auxiliary theorem.
The full refactored module compiled in 4.2 seconds before cosmetic cleanup.

No existing declaration changes its signature or visibility. In particular the
unused instance binders of `supportOpenBaseChangeApp_naturality` are retained;
its unused-section-variable linter is disabled only for this theorem to preserve
that interface. The new natural transformation is explicit data, with no choice
and no postponed proof.

## Old

```lean
noncomputable def supportOpenBaseChangeApp
    {X' U' : Scheme.{u}} (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
    [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) v).obj
        ((upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j).obj M) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) j' ⋙ lowerStar (ModuleCat.{u + 1} Λ) j').obj
        ((upperStar (ModuleCat.{u + 1} Λ) v).obj M) :=
  (baseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.symm)).app
      ((upperStar (ModuleCat.{u + 1} Λ) j).obj M) ≫
    (lowerStar (ModuleCat.{u + 1} Λ) j').map
      (((upperStarComp (ModuleCat.{u + 1} Λ) vU j).symm ≪≫
        upperStarCongr (ModuleCat.{u + 1} Λ) sq ≪≫
        upperStarComp (ModuleCat.{u + 1} Λ) j' v).hom.app M)
```

## New

```lean
noncomputable def supportOpenBaseChange
    {X' U' : Scheme.{u}} (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
    [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v) :
    (upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j) ⋙
        upperStar (ModuleCat.{u + 1} Λ) v ⟶
      upperStar (ModuleCat.{u + 1} Λ) v ⋙
        (upperStar (ModuleCat.{u + 1} Λ) j' ⋙ lowerStar (ModuleCat.{u + 1} Λ) j') :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) j)
      (baseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.symm)) ≫
    Functor.whiskerRight (((upperStarComp (ModuleCat.{u + 1} Λ) vU j).symm ≪≫
      upperStarCongr (ModuleCat.{u + 1} Λ) sq ≪≫
      upperStarComp (ModuleCat.{u + 1} Λ) j' v).hom)
      (lowerStar (ModuleCat.{u + 1} Λ) j')

/-- The canonical quotient comparison for a commutative open square and etale vertical
maps: pushforward base change followed by the inverse-image composition comparison.
Source: blueprint def-pur-triangle-meaning; Stacks Tag 09BN
(blueprint: def-pur-triangle-meaning). -/
noncomputable def supportOpenBaseChangeApp
    {X' U' : Scheme.{u}} (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
    [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) v).obj
        ((upperStar (ModuleCat.{u + 1} Λ) j ⋙ lowerStar (ModuleCat.{u + 1} Λ) j).obj M) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) j' ⋙ lowerStar (ModuleCat.{u + 1} Λ) j').obj
        ((upperStar (ModuleCat.{u + 1} Λ) v).obj M) :=
  (supportOpenBaseChange Λ j v vU j' sq).app M
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SupportTriangleCompatibility --uses
supportOpenBaseChangeApp` finds no external textual user of the changed definition.
The following complete transitive importer list is included for completeness.
The sole direct importer is `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle`;
it needs no source adaptation. No target signature, predicate or chosen map changes:
the application unfolds to exactly the old composite, including its direction and
all components. Thus every target using these definitions has the same meaning;
the independent reader should verify this definitional equality in the usual
review of a definition change. No target statement is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SupportTriangleCompatibility | G7 | definition refactored and theorem proved |
| Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison | unclaimed | unchanged; same definition by reduction |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | unchanged; same definition by reduction |
| Sheaf.AlgebraicGeometry.SupportLocalizationTriangle | A8 | unchanged; same definition by reduction |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | unchanged; same definition by reduction |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | unchanged; same definition by reduction |
| Sheaf.Paper.AdicPurityObjects | W9 | unchanged; same definition by reduction |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | unchanged; same definition by reduction |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | unchanged; same definition by reduction |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | unchanged; same definition by reduction |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.ArithmeticRoots | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.ChernFlagFormula | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | unchanged; same definition by reduction |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteReductionComparisons | T7 | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | unchanged; same definition by reduction |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | unchanged; same definition by reduction |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.FourierTraceFormula | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.LocalizedTopChern | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.PurAdicReconstruction | H8 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityChernClasses | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | F1 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.PurityDncComparisons | G3 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityDncInvariance | H2 | unchanged; same definition by reduction |
| Sheaf.Paper.PurityGysinStructure | F1 | unchanged; same definition by reduction |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | unchanged; same definition by reduction |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | unchanged; same definition by reduction |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | unchanged; same definition by reduction |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.SmoothPurityMap | R2 | unchanged; same definition by reduction |
| Sheaf.Paper.SmoothTrace | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | unchanged; same definition by reduction |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.WeilFourierInversion | J6 | unchanged; same definition by reduction |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.WeilOne | unclaimed | unchanged; same definition by reduction |
| Sheaf.Paper.ZlShriekComposition | unclaimed | unchanged; same definition by reduction |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | unchanged; same definition by reduction |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | unchanged; same definition by reduction |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | unchanged; same definition by reduction |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | unchanged; same definition by reduction |
| TargetsCheck | unclaimed | unchanged; same definition by reduction |
| WeilConjectures | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.Statement | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.Curve | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.Examples | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | unchanged; same definition by reduction |
| WeilConjectures.ZetaFunction.Weights | unclaimed | unchanged; same definition by reduction |

## Status

landed 20261019T093423-L-2309320 2026-10-19 (merge of deliver/G7/Sheaf.AlgebraicGeometry.SupportTriangleCompatibility)
