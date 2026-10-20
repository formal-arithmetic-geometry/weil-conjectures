# AdicLocalCharacteristicFactor private helper universe

## Reason

Preflight requires a record for the additional universe command used by the private,
proved linear-algebra helper `mapped_charpolyRev`. The scalar field, extension field,
and module carrier have independent universes. The new universe names no public
parameter: all original public declarations keep exactly their original universe
parameters, binders, visibility and definitions. All new imports in the assigned
module are proof-only. No target meaning changes and no consumer adaptation is needed.

## Old

```lean
universe u v
```

## New

```lean
universe u v w
```

## Users

The source-only downstream check lists the following 27 consumers. Its `--uses
sfLocalCharacteristicFactor` check finds only the assigned module and
`Sheaf.Paper.RealSheavesCohomologyEulerSeries`; their public expressions are unchanged.
No consumer is edited, so no adaptation claim is required. Holder status is not
queried for unchanged consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicLocalCharacteristicFactor | G5 | Private proof universe only; existing signatures unchanged. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not queried; not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | not queried; not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not queried; not adapted | Unchanged public interface; no adaptation. |
| Sheaf.Paper.WeilOne | not queried; not adapted | Unchanged public interface; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried; not adapted | Unchanged public interface; no adaptation. |
| TargetsCheck | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.Statement | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; not adapted | Unchanged public interface; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | not queried; not adapted | Unchanged public interface; no adaptation. |

## Status

landed 20261020T051319-L-1632546 2026-10-20 (merge of deliver/G5/Sheaf.Paper.AdicLocalCharacteristicFactor)
