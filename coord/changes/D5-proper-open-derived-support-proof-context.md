# AlgebraicGeometry.Scheme.isIso_proper_open_derived_support

## Reason

The preflight requires a change record for the added `section`, scoped instance-attribute
commands and `open CategoryTheory.Limits`, alongside private proved helpers. They fix the
sheafification and ordinary derived-localization instances at the coefficient universes
already specified by the original theorem. The six removed instance attributes are scoped
to the section ending at the bottom of this file. The replacement instances are private
and local. No consumer inherits the temporary instance search choices.

All original public imports and the sole public theorem's signature are preserved.
Every added import is proof-only. No existing definition or target statement changes,
and no module other than the assigned item is adapted. No target meaning review reopens.

## Old

Original declaration signature, verbatim:

```lean
theorem isIso_proper_open_derived_support
    {X T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (_comm : j₁ ≫ f = j₂) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) :
    IsIso ((exceptionalOpenAdjunction j₂ A).counit.app
      ((proEtaleConstantDerivedDirectImage f A).obj ((sfIntrinsicDerivedOpen A j₁).obj K)))
```

Original command context, verbatim:

```lean
@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme
```

## New

The same public signature now has a complete proof:

```lean
theorem isIso_proper_open_derived_support
    {X T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (_comm : j₁ ≫ f = j₂) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) :
    IsIso ((exceptionalOpenAdjunction j₂ A).counit.app
      ((proEtaleConstantDerivedDirectImage f A).obj ((sfIntrinsicDerivedOpen A j₁).obj K)))
```

New command context and private local instance declarations, verbatim:

```lean
@[expose] public section

set_option autoImplicit false

section

-- Keep the ordinary localization and coefficient sizes fixed while elaborating the proof.
attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable local instance (priority := 3000) fixed_sheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private noncomputable local instance (priority := 3000) fixed_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private noncomputable local instance fixed_derived (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 2} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  HasDerivedCategory.standard _

-- All remaining helpers are private; the original public theorem follows.

```

The private `fixed_kInjective` local instance below uses the existing
`proEtaleRingModules_hasKInjectiveResolutions` instance. Both the namespace and outer
section are closed after the public theorem.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport
--uses isIso_proper_open_derived_support` found 195 transitive consumers. The only
external declaration-use hit is `Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint`.
It applies the unchanged theorem. The other consumers inherit the same public API
and definitions; the new helpers and imports are private. No adaptation is needed.
The table lists every consumer and current claim holder from the source scan.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | D5 | Same public signature and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | K1 | Same public signature and definitions; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | K6 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | D2 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | Y6 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | E5 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | U5 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Same public signature and definitions; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same public signature and definitions; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Same public signature and definitions; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same public signature and definitions; no adaptation. |
| TargetsCheck | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same public signature and definitions; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same public signature and definitions; no adaptation. |

## Status

landed 20261019T231107-L-547381 2026-10-19 (merge of deliver/D5/Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport)
