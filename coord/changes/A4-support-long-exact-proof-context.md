# Sheaf.AlgebraicGeometry.SupportLongExact

## Reason

The proof of `AlgebraicGeometry.exists_support_longExact` uses private helpers with
separately specified derived-category universes. The static interface check requires a
record for the extra module-local universe and variable commands. They do not change
any existing declaration's signature or any definition's body. The new module
`Sheaf.CategoryTheory.DerivedInjectiveBoundary` supplies a proved generic API for the
normalized connecting transformations. Its import in the item is proof-only.

## Old

```lean
universe c v a w u
```

There was no private proof-helper section between `SupportSequencePairNatural` and
`AlgebraicGeometry.Etale.supportSequenceCoefficients`; the sole theorem proof was `by sorry`.
The generic module did not exist. All original public declarations and their signatures
are preserved verbatim in the delivery, including the full statement of
`AlgebraicGeometry.exists_support_longExact`.

## New

```lean
universe c v a w u d e
```

The added private-helper section has this local context:

```lean
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type a) [Category.{w} A] [Abelian A] [HasSheafify J A]
variable [EnoughInjectives (Sheaf J A)] [HasDerivedCategory.{d} (Sheaf J A)]
variable [HasDerivedCategory.{e} A] {V W : C} (j : W ⟶ V)
```

Its helpers prove the zero composite, exactness of the support row on injectives,
existence and exactness of the normalized boundary, and its pair naturality. A further
private theorem proves injective module-sheaf restriction surjectivity using free module
presheaves. The two backward elaboration options are scoped to individual private
proofs. Universe and variable commands do not export variables or instances to importers.
The existing public definitions, declaration types, and public imports are unchanged;
no target meaning changes. The fixed-unit proof import
`Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` is retained.

The new generic module exports `injectiveHomologyModelIso`,
`injectiveHomologyModelIso_natTrans` (with its reassociated version),
`injectiveBoundaryRow`, `injectiveBoundaryRow_shortExact`,
`InjectiveBoundaryNormalized`, `exact_transport`, `injectiveBoundary_exact`, and
`exists_injectiveBoundary` in `CategoryTheory.Functor`. The node
`lem-pur-derived-injective-boundary` records this proved construction and its API.
Every definition is a construction and every theorem is proved, with zero added holes.
The item imports this API privately, so it is not re-exported to its consumers.

## Users

This table contains the item and all transitive downstream modules from the source
import-graph scan on 2026-10-19. Holders are read from the current claim records.
No downstream source is edited. Existing public definitions and declaration types are
unchanged, so every user's hypotheses and conclusions keep the same meaning. The
textual declaration-use scan finds `exists_support_longExact` and
`SupportSequencePairNatural` only in the item; `SupportSequenceExact` is also used in
`RetractedSupportLocalizationComparison`, `SupportComparisonBoundary`, and
`PurityAffineLineOrientation`, whose signatures and definitions require no adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SupportLongExact | A4 | Proof completed; existing signatures, definitions and public imports preserved. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | A3 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | S2 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | F1 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | H2 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | F1 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | F2 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | H4 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged signatures and meaning; no adaptation. |
| TargetsCheck | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Z8 | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | B4 | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | C1 | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | C3 | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | D2 | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged signatures and meaning; no adaptation. |
| Sheaf.CategoryTheory.DerivedInjectiveBoundary | A4 (new) | New proved generic API; privately imported by the item. |

## Status

landed 20261019T154002-L-3023490 2026-10-19 (merge of deliver/A4/Sheaf.AlgebraicGeometry.SupportLongExact)
