# SmoothPurityTowerInjectiveComponents proof context

## Reason

Complete the remaining injective-component proof without changing existing public signatures,
definition bodies, visibility, public imports or docstrings. Fully proved private helpers
handle the module equivalence to the small site and the section-acyclicity comparisons.
The existing ordinary evaluation adjunction proves product preservation; no pointwise-limit
construction remains. The source has no new public declaration.

Generic coefficient naturality, presheaf pushforward finite-limit preservation and
identity-on-sections uniqueness are proved before instantiating the concrete coefficients.
Explicit universes and separately elaborated section equalities avoid expensive unification.
The module-local backward definitional-equality options permit comparison of the existing
coefficient and direct-image constructions. They do not propagate to importers. The
helper instance attributes on `small_module_evaluation_additive` and `levelPush_additive`
are local.
The complete module compiled cleanly in 21.2 seconds under the unchanged 60-second limit.
No temporary profiler or heartbeat option remains. No consumer needs adaptation.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```

`sp_tower_injective_components` has proof `by sorry` and no preceding private acyclicity helpers.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
```

All existing signatures and definition bodies are identical. The sole remaining theorem hole
has a complete proof from existing declarations and fully proved private helpers.

## Users

The source-only import graph has 90 transitive consumers, recorded below. Direct importers are `SmoothPurityTowerLevels` and `SmoothPurityTowerShriekLevels`. No consumer file is
edited; all see identical public signatures, definitions, and public import closure.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | T4 | Final proof completed; private proof context only. |

| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerLevels | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | claimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same public declarations and imports; no adaptation. |
| TargetsCheck | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same public declarations and imports; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same public declarations and imports; no adaptation. |

## Status

landed 20261020T132042-L-1407135 2026-10-20 (merge of deliver/T4/Sheaf.Paper.SmoothPurityTowerInjectiveComponents)
