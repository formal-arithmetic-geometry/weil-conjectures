# WeilConjectures.constructible_flat_cohomology_tor_bound

## Reason

The stage-3 dry run conservatively classifies added `universe`, `open`, and local
instance commands as an importer-visible change and requires this record. They support
five private, proved helpers used to fill the existing theorem's proof. Every existing
public declaration, signature, visibility, instance and public import is preserved.
The added commands are file-local elaboration context; no consumer is adapted.

## Old

```lean
universe t u
```

There was no `open MonoidalCategory` command or the following local instance attribute.
The public theorem had this signature and a single `sorry` proof:

```lean
theorem constructible_flat_cohomology_tor_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (V : Scheme.{t}) [IsAffine V]
    (_hV : (ProEt.topology V).IsWeaklyContractible.{max u (t + 1)} (ProEt.mk (𝟙 V)))
    (K : DerivedCategory (scalarReductionSource l E V))
    (_hcomplete : IntegralOnSlice.IsComplete l E V none K)
    (a b : ℤ) (_hab : a ≤ b)
    (_hbounded : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((scalarReductionDerivedExtension l E V 0).obj K)))
    (_hlocal : ∀ q : ℤ,
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses V
        (Padic.coefficientExtensionRing l E 1)
        (fun M ↦ Module.Finite (ULift.{t + 1} (Padic.coefficientExtensionRing l E 1)) M)
        ((DerivedCategory.homologyFunctor _ q).obj
          ((scalarReductionDerivedExtension l E V 0).obj K))) :
    ∀ (U : V.ProEt)
      (L : SheafOfModules.{max u (t + 1)} ((integralCoefficientSheaf l E V 0).over U))
      (i : ℤ), i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (SheafOfModules.ringedSiteDerivedTensorOfUniverses.{t + 1, t,
            max u (t + 1), (max u (t + 1)) + 1}
          ((integralCoefficientCommRingSheaf l E V 0).over U)
          (ringedSiteDerivedRestrictionOfUniverses.{t + 1, t, max u (t + 1),
              max u (t + 1), (max u (t + 1)) + 1, (max u (t + 1)) + 1}
            (integralCoefficientSheaf l E V 0) U
            ((scalarReductionDerivedExtension l E V 0).obj K))
          ((DerivedCategory.singleFunctor _ 0).obj L)))
```

## New

```lean
universe t u c v r w
open MonoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
```

The public theorem signature above is unchanged verbatim, and its proof is complete.
The added universe names occur only in private helpers. Namespace opening changes name
resolution inside this file. The instance attributes are local to its section, so they
are not exported. There are no new public declarations. All proof imports are non-public.
No definition changes, and no target-statement meaning or review changes.

## Users

`tools/downstream.py Sheaf.Paper.ConstructibleFlatCohomologyTorBound
--uses constructible_flat_cohomology_tor_bound` found only this file mentioning the
name, plus 170 transitive importers. All are listed below. The source-level consumer
check is that every public signature and public import is preserved and each new
helper is private; no importer needs an adaptation. Ownership is irrelevant to these
untouched consumers and is not changed by this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | C1 | Same signature; proof completed. |
| Sheaf.DeligneLaumon.GenericDualityModel | not adapted | Same public interface; no change. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not adapted | Same public interface; no change. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted | Same public interface; no change. |
| Sheaf.DeligneLaumon.Reduction.Composition | not adapted | Same public interface; no change. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not adapted | Same public interface; no change. |
| Sheaf.Paper.AdicExceptionalCoherence | not adapted | Same public interface; no change. |
| Sheaf.Paper.AdicExceptionalComposition | not adapted | Same public interface; no change. |
| Sheaf.Paper.AdicExceptionalOperations | not adapted | Same public interface; no change. |
| Sheaf.Paper.AdicExceptionalProjection | not adapted | Same public interface; no change. |
| Sheaf.Paper.AdicExceptionalProjectionData | not adapted | Same public interface; no change. |
| Sheaf.Paper.AdicExceptionalScalars | not adapted | Same public interface; no change. |
| Sheaf.Paper.ArithmeticRoots | not adapted | Same public interface; no change. |
| Sheaf.Paper.ChernFlagFormula | not adapted | Same public interface; no change. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted | Same public interface; no change. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted | Same public interface; no change. |
| Sheaf.Paper.CompactSupportLerayFiltration | not adapted | Same public interface; no change. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted | Same public interface; no change. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted | Same public interface; no change. |
| Sheaf.Paper.ExtensionByZeroPunctual | not adapted | Same public interface; no change. |
| Sheaf.Paper.FieldShriekCompositionQcqs | not adapted | Same public interface; no change. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not adapted | Same public interface; no change. |
| Sheaf.Paper.FiniteRegularReductionDualizing | not adapted | Same public interface; no change. |
| Sheaf.Paper.FlagPullbackInjective | not adapted | Same public interface; no change. |
| Sheaf.Paper.FourierTraceFormula | not adapted | Same public interface; no change. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not adapted | Same public interface; no change. |
| Sheaf.Paper.LocalizedTopChern | not adapted | Same public interface; no change. |
| Sheaf.Paper.ProjectiveBundleFormula | not adapted | Same public interface; no change. |
| Sheaf.Paper.PurityChernClasses | not adapted | Same public interface; no change. |
| Sheaf.Paper.QbarMiddleTStructure | not adapted | Same public interface; no change. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not adapted | Same public interface; no change. |
| Sheaf.Paper.RationalRealizationTensorComparison | not adapted | Same public interface; no change. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted | Same public interface; no change. |
| Sheaf.Paper.SfBidualityClass | not adapted | Same public interface; no change. |
| Sheaf.Paper.SupportedProjectionSplitting | not adapted | Same public interface; no change. |
| Sheaf.Paper.TateTwistLisseLine | not adapted | Same public interface; no change. |
| Sheaf.Paper.TateTwistSupportCondition | not adapted | Same public interface; no change. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Same public interface; no change. |
| Sheaf.Paper.VectorBundleThomClass | not adapted | Same public interface; no change. |
| Sheaf.Paper.VerdierExchange | not adapted | Same public interface; no change. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not adapted | Same public interface; no change. |
| Sheaf.Paper.WeilFourierInversion | not adapted | Same public interface; no change. |
| Sheaf.Paper.WeilFourierPlancherel | not adapted | Same public interface; no change. |
| Sheaf.Paper.WeilOne | not adapted | Same public interface; no change. |
| Sheaf.Paper.WfTensorCompletionFrobenius | not adapted | Same public interface; no change. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not adapted | Same public interface; no change. |
| Sheaf.Paper.ZlShriekComposition | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.CoefQbarVerdier | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.CompositionProjectionMate | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.GeneratorReductionStatement | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.OpenAdjunctionShift | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.OpenFactorCoherence | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.OpenFactorPullModel | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.OpenFactorTensorModel | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.QbarDualRecollement | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.RationalOperations | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.RationalVerdier | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not adapted | Same public interface; no change. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not adapted | Same public interface; no change. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted | Same public interface; no change. |
| TargetsCheck | not adapted | Same public interface; no change. |
| WeilConjectures | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted | Same public interface; no change. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not adapted | Same public interface; no change. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not adapted | Same public interface; no change. |
| WeilConjectures.Statement | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.Curve | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.EulerProduct | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierInversion | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierStalk | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.FourierTrace | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.LFunction | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.VerdierDual | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not adapted | Same public interface; no change. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.Examples | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.LissePurity | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.Rationality | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | Same public interface; no change. |
| WeilConjectures.ZetaFunction.Weights | not adapted | Same public interface; no change. |

## Status

landed 20261019T093302-L-2288982 2026-10-19 (merge of deliver/C1/Sheaf.Paper.ConstructibleFlatCohomologyTorBound)
