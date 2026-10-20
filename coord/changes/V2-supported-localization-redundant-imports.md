# SupportedLocalizationComparisons public imports

## Reason

Remove two redundant direct imports after proving all local holes. Both removed modules
are still public transitive dependencies, so the available declarations and instances
are identical for every consumer. No definition or theorem signature changes.

`NormalizedSupportTriangle` publicly imports `SupportedExteriorProduct`.
The latter publicly imports `EtaleSupportedSections`, then `DerivedCategories`,
`WeilConjectures.AlgebraicGeometry.DerivedCategories`,
`SixFunctors.Etale.Derived.Coefficients`, `SixFunctors.Etale.Derived.Tensor`,
`CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, and finally
`CategoryTheory.DerivedCategory.Monoidal.Shift` (all under the `WeilConjectures`
root after the first three Sheaf modules).

## Old

```lean
public import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
```

## New

```lean
public import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
```

## Users

All 81 transitive importers listed by `tools/downstream.py` appear below.
The sole direct importer is `Sheaf.AlgebraicGeometry.SupportedProductLocalization`.
The public import closure is identical by the paths above, hence no consumer requires
an adaptation and no target meaning changes. Claim information is the shared checkout's
current record; no held consumer is edited.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.KunnethSupported` | X3 | Identical public import closure; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | V2 | Identical public import closure; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.CartierClassAgreement` | U5 | Identical public import closure; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | Identical public import closure; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | E5 | Identical public import closure; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.PurityDivisorClass` | J7 | Identical public import closure; no adaptation. |
| `Sheaf.Paper.PurityFrameIndependence` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.RegularImmersionCancellation` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.RegularImmersionClassData` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.RegularImmersionExteriorClass` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurity` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.RegularImmersionSignedEvaluation` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.RelativeSupportBottomDescent` | D9 | Identical public import closure; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Identical public import closure; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Identical public import closure; no adaptation. |
| `TargetsCheck` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Identical public import closure; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Identical public import closure; no adaptation. |

## Status

landed 20261020T131204-L-1256044 2026-10-20 (merge of deliver/V2/Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons)
