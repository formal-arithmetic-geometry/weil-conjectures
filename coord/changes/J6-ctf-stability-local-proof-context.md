# constructibleFiniteTor_stability_direct_images proof context

## Reason

The static delivery check classifies the module-local irreducibility attribute as a
possible interface change. It prevents elaboration from expanding the coefficient pullback
and derived tensor constructions. Both attributes are local to this module's namespace;
they export no attributes or instances. Existing declarations, definitions, universes,
visibility, and public imports are unchanged. No target changes meaning.

## Old

No local irreducibility command preceded the theorem. Its proof was `by sorry`.
The existing declaration signature remains verbatim identical, as checked against the
current shared source. No definition is changed.

## New

```lean
-- Avoid expanding the coefficient pullback and the derived monoidal construction.
attribute [local irreducible] upperStarFromPoint derivedTensor
```

The theorem now has a complete proof from the listed interfaces and two separately
sourced statements. Conjunction assembly uses the explicit constructor
`refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩`; the tensor-amplitude calculation unfolds only
`derivedTensor` and `MonoidalCategory.curriedTensor` with `simpa only`.
The local attribute ends with the enclosing namespace. No downstream file is adapted.

## Users

`tools/downstream.py Sheaf.SixFunctors.CtfStabilityDirectImages --uses
constructibleFiniteTor_stability_direct_images` lists 193 transitive importing modules.
The theorem name occurs only in the item itself. All listed consumers are below; the
claims are a snapshot and no consumer is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Proof and local elaboration commands only; public signature unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | N1 | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Unchanged interface; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | Q1 | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Unchanged interface; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | R5 | Unchanged interface; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Unchanged interface; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | N4 | Unchanged interface; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged interface; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Unchanged interface; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unchanged interface; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Unchanged interface; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Unchanged interface; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Unchanged interface; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A6 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | Q8 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | T8 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | P4 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | H6 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | K1 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | G8 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | R6 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Unchanged interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged interface; no adaptation. |
| TargetsCheck | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged interface; no adaptation. |

## Status

landed 20261020T051421-L-1674693 2026-10-20 (merge of deliver/J6/Sheaf.SixFunctors.CtfStabilityDirectImages)
