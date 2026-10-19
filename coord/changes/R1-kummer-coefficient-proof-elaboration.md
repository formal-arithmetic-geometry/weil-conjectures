# AlgebraicGeometry.Scheme.kummer_coefficient_base_change proof elaboration

## Reason

The completed finite-basis proof uses the existing monoidal tensor notation on
module presheaves and unfolds definitionally equal biproduct terms during backward
elaboration. The stage-3 checker conservatively records changes to open and
set_option commands as an interface change, so this record inventories the users.
The added namespace opening is local to this module, and the transparency option
is scoped to the one theorem. Importers inherit neither command. All existing
public signatures, definitions, instances and visibility remain identical.
No target statement or definition used by a target changes its meaning.

The three new modules contain five proved public helper theorems, recorded by
three new DAG nodes. They add no instances or axioms. They are private imports of
the item and do not alter its public-import list. All private helpers are proved
or explicitly constructed; none changes an existing declaration.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

The existing theorem had no local backward-elaboration option and its proof was
sorry. Its full signature and the KummerIntegralLiftBoundary definition are
unchanged, verbatim, in the new version.

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
```

The existing theorem declaration is now preceded by:

```lean
set_option backward.isDefEq.respectTransparency false in
```

Its complete proof constructs the normalized coefficient comparison, descends the
Kummer boundary by the tensor universal property and proves compatibility with
every specified integral lift by the short-complex naturality equation.
The new modules use autoImplicit false and a local transparency option for their
own elaboration. Their theorem signatures and natural-language proofs are in
KummerFiniteFreeComparison, KummerFiniteBiproducts and KummerIntegralRootComparison.

## Users

The required command
`python3 tools/downstream.py Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange
--uses kummer_coefficient_base_change` lists 171 transitive importers and finds no
textual use of the theorem outside its own declaration. The table inventories all
171 plus the item, with the current claim holder. No existing consumer is edited.
The unchanged statements and data remain available to every importer; namespace
openings and theorem-local elaborator options are not imported. Consequently the
statements of every listed consumer keep their meanings and need no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange | R1 | Proof elaboration only; existing public interface preserved. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No effect; no source adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | No effect; no source adaptation. |
| Sheaf.Paper.AdicPurityObjects | W9 | No effect; no source adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | No effect; no source adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | No effect; no source adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | No effect; no source adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | No effect; no source adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No effect; no source adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | No effect; no source adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | No effect; no source adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | No effect; no source adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | No effect; no source adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | No effect; no source adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | No effect; no source adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | No effect; no source adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | No effect; no source adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | F1 | No effect; no source adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | No effect; no source adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | No effect; no source adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | No effect; no source adaptation. |
| Sheaf.Paper.PurityDncInvariance | H2 | No effect; no source adaptation. |
| Sheaf.Paper.PurityRelativeKummer | F4 | No effect; no source adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | No effect; no source adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No effect; no source adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No effect; no source adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | No effect; no source adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | No effect; no source adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | No effect; no source adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No effect; no source adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | No effect; no source adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No effect; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | No effect; no source adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No effect; no source adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No effect; no source adaptation. |
| TargetsCheck | unclaimed | No effect; no source adaptation. |
| WeilConjectures | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No effect; no source adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No effect; no source adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No effect; no source adaptation. |
| WeilConjectures.Statement | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No effect; no source adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No effect; no source adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No effect; no source adaptation. |

| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No effect; no source adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No effect; no source adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | No effect; no source adaptation. |

## Status

landed 20261019T112515-L-3948727 2026-10-19 (merge of deliver/R1/Sheaf.AlgebraicGeometry.KummerCoefficientBaseChange)
