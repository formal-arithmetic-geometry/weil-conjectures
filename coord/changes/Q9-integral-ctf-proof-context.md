# WeilConjectures.integral_ctf_isTriangulated

## Reason

The proved zero-object argument uses the zero-object notation and lemmas from
`CategoryTheory.Limits`. The preflight conservatively treats the added `open`
commands as an interface change. They only resolve names in this file: no public
signature, definition, instance, notation declaration, or public import changes.
The only textual change in the theorem signature is alpha-renaming the unused
instance lambda binder from `n` to `_n`, following the compiler warning. Its
elaborated type is identical. All proof helpers are private
and proved; the item adds no holes.

## Old

```lean
open CategoryTheory AlgebraicGeometry.Scheme
```

The explicit instance argument in the theorem signature was:

```lean
(fun (n : ℤ) ↦ inferInstance)
```

## New

```lean
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open scoped ZeroObject
```

The corresponding explicit instance argument is now:

```lean
(fun (_n : ℤ) ↦ inferInstance)
```

All surrounding binders, universes, instance arguments, and conclusions are
verbatim unchanged. The renamed variable is bound only within this lambda, so
this does not rename or change any parameter of the theorem.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralCtfTriangulated --uses
integralCtfProperty` reports the following complete import downstream closure.
Its only direct user of the property outside this file is
`Sheaf.Paper.PurAdicScalarExtensionTorBound`; there is no direct use of the
triangulation theorem outside its own module. The property and theorem retain their
signatures and the property retains its definition, so all consumers retain the
same meaning and require no adaptation. The added opens do not create exported
notation or alter any target's definition or statement; no target statement review
is reopened. Public imports remain identical, and only unused proof imports are
removed. No module held by another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCtfTriangulated | Q9 | Prove original theorem; add private proof helpers and local name resolution. |
| Sheaf.DeligneLaumon.GenericDualityModel | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteTorStability | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.PurityChernClasses | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.SfBidualityClass | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.WeilOne | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| TargetsCheck | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.Statement | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | Not edited; claim unaffected | Same public declarations and public imports; no adaptation. |

## Status

landed 20261019T231313-L-571745 2026-10-19 (merge of deliver/Q9/Sheaf.Paper.IntegralCtfTriangulated)
