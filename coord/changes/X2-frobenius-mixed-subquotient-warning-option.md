# FrobeniusModule.IsMixedOfWeightsAtMost.subquotient

## Reason

Repair the returned delivery `58afaa263`: the landing scanner attributed the
`set_option warn.sorry false` command at line 27 as an unnamed hole. Remove the
warning suppression from this fully proved module. The dry run conservatively
classifies removal of a file-level command as a change requiring this record.
The option is local to the file: removing it changes neither exported declarations
nor importer options. The theorem signature, definitions and public imports stay identical.

## Old

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
```

## Users

`tools/downstream.py` lists the 28 transitive consumers below. Its declaration-use
scan finds the declaration in the item itself and two applications in
`Sheaf.Paper.MixedWeightsStability`. The direct importers are
`Sheaf.DeligneLaumon.Reduction.AffineCurveUpper`,
`Sheaf.Paper.CurveMiddleExtensionUpper` and `Sheaf.Paper.MixedWeightsStability`.
Their statements and proofs see identical declaration types. No consumer needs
adaptation. Only the assigned module is edited. Holders are from the current
claim records when preparing this repair.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient` | X2 | Proof completed; remove local warning suppression. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Same declarations and meaning; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Same declarations and meaning; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Same declarations and meaning; no adaptation. |
| `Sheaf.Paper.MixedWeightsStability` | G4 | Same declarations and meaning; no adaptation. |
| `Sheaf.Paper.WeilOne` | unclaimed | Same declarations and meaning; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Same declarations and meaning; no adaptation. |
| `TargetsCheck` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.Statement` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Same declarations and meaning; no adaptation. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Same declarations and meaning; no adaptation. |

## Status

landed 20261020T131229-L-1263767 2026-10-20 (merge of deliver/X2/Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient)
