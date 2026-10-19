# AlgebraicGeometry.ProEtale.reductionEtaleTateExtensionMap

## Reason

Expose the existing degree-zero adjoint-transpose expression as the generic definition
`reductionSingleAdjointTranspose`. This lets the K-flat representative proof compare maps in
abstract abelian categories before specializing to the large ordinary étale sheaf categories.
The old and new definitions have the same type and are definitionally equal after unfolding
this single new helper. The root-normalized map and the chosen derived adjunction are unchanged.
There is no mathematical change, including to target statements or their meaning.

## Old

```lean
def reductionEtaleTateExtensionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (Etale.scalarExtension φ T).obj (Etale.ordinaryFiniteLine A N hA T) ⟶
      Etale.ordinaryFiniteLine B N hB T :=
  ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology φ)).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor _ 0).map (reductionEtaleTateMap φ T N hA hB) ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
        0).inv.app (finiteEtaleTateLine T N B hB))
```

## New

```lean
def reductionEtaleTateExtensionMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    (Etale.scalarExtension φ T).obj (Etale.ordinaryFiniteLine A N hA T) ⟶
      Etale.ordinaryFiniteLine B N hB T :=
  show (Etale.scalarExtension φ T).obj
      ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateLine T N A hA)) ⟶
    (DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateLine T N B hB) from
  reductionSingleAdjointTranspose (Sheaf.restrictScalars T.smallEtaleTopology φ)
    (Etale.scalarExtension φ T)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars.{u} T.smallEtaleTopology φ))
    (reductionEtaleTateMap φ T N hA hB)
```

The new generic helper is the old right-hand side with its categories, exact functor,
adjunction and ordinary map made explicit parameters. Its defining expression is:

```lean
(a.homEquiv _ _).symm
  ((DerivedCategory.singleFunctor C 0).map g ≫
    (U.mapDerivedCategorySingleFunctor 0).inv.app Q)
```

## Users

`tools/downstream.py Sheaf.SecSmoothPurity.ReductionExceptional --uses
reductionEtaleTateExtensionMap` lists the following transitive consumers. The only direct textual
uses are in the item itself. No consumer requires an adaptation: every existing signature is
unchanged and the new expression reduces to the old one. The generic helper is not an additional
hypothesis or a chosen comparison isomorphism. All consumers retain exactly their statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | Proof uses the generic transpose; existing signatures unchanged. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.ChernFlagFormula | G4 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | U5 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteFreeProjectionExchange | K8 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.LocalizedTopChern | E5 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.SfBidualityClass | C6 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.WeilFourierInversion | J6 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Unchanged: no direct use; definitionally equal refactoring. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| TargetsCheck | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.Statement | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged: no direct use; definitionally equal refactoring. |

## Status

landed 20261019T192747-L-1863887 2026-10-19 (merge of deliver/G8/Sheaf.SecSmoothPurity.ReductionExceptional)
