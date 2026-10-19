# AlgebraicGeometry.Scheme.proEtale_supported_constant_presentation

## Reason

The completed proof introduces a balanced `namespace ProEt` and `noncomputable section`,
with section variables for private continuous-function constructions. The static
interface check conservatively records those commands as an interface change. This
record documents their scope and every downstream consumer for independent review.
All original public definitions, their signatures and bodies, and the theorem signature
are unchanged. All added declarations are private. All original public imports remain
public; new imports are private proof dependencies. No global instance, notation or
attribute is introduced. The transparency options apply to individual helper declarations.

## Old

The original outer namespace is `AlgebraicGeometry.Scheme`; it has no nested `ProEt`
proof section. Its existing public theorem has this exact signature:

```lean
theorem proEtale_supported_constant_presentation (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ h : proEtaleOpenConstantCounit i.openComplement.ι A ≫
        proEtaleClosedConstantRestriction i A = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (proEtaleClosedConstantRestriction i A) h))
```

## New

The same public theorem retains this exact signature:

```lean
theorem proEtale_supported_constant_presentation (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ h : proEtaleOpenConstantCounit i.openComplement.ι A ≫
        proEtaleClosedConstantRestriction i A = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (proEtaleClosedConstantRestriction i A) h))
```

Between the three unchanged public definitions and the public theorem, the proof now
uses these balanced scope commands (the intervening declarations are all private):

```lean
namespace ProEt

noncomputable section

variable (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
  [TopologicalSpace R] [DiscreteTopology R]
```

Both scopes close before the helpers for the original cokernel theorem:

```lean
end

end ProEt
```

The complete new helper definitions and proofs are in the delivered module. The public
statement is proved by a zero composite, epimorphic closed restriction and the kernel
property of the open counit. No consumer statement changes meaning; no consumer edit
is required. In particular, `Sheaf.Paper.SupportedSectionsHom` consumes precisely the
same cokernel cofork and still transports it through its original comparison isomorphisms.
No target definition or signature changes, so no target statement review is reopened.

## Users

`tools/downstream.py` finds the following transitive consumers. Holdings are the current
claim records at preparation. Because every public definition and signature is identical,
each consumer retains exactly the same objects, arrows and statements. The only direct
textual use of the theorem is in `Sheaf.Paper.SupportedSectionsHom`; its proof consumes
the same existential cokernel result. Other consumers inherit this unchanged interface.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | G7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedCohomologyHom | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedCup | S5 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedHomAdjunctionTranspose | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | H4 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedSectionsHom | unclaimed | Same cokernel theorem signature and definitions; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Public signatures and definitions unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Public signatures and definitions unchanged; no adaptation. |

## Status

landed 20261019T122633-L-478222 2026-10-19 (merge of deliver/R3/Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation)
