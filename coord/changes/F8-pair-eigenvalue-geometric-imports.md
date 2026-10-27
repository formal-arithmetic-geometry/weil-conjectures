# Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent public imports

## Reason

The statement needs the source sheaf, lissity, smoothness and geometric-connectedness interfaces. RealCurve and its weight/purity theory are not used. Profiling with that import showed loading dominated the compile; the new structural statement itself elaborated in under a second. Remove the unnecessary heavyweight import rather than splitting a slow proof.

## Old

```lean
public import WeilConjectures.DeligneLaumon.Reduction.RealCurve
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.LisseFiltration
```

The theorem signature stays verbatim. Proof-only imports add the new orbit lemma, geometric irreducibility under isomorphism, and stalk isomorphisms. No target definition or statement changes.

## Users

The declaration-name search reports only the item itself and PairEigenvalueCurveTest. The sole direct Lean importing module, PairEigenvalueCurveTest, already publicly imports RealCurve independently. Consequently all its transitive users retain that interface. The unchanged direct consumer was compiled successfully against the new files. No consumer edits are necessary. The full downstream list is recorded below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent | F8 | Import reduction and completed proof; signature identical. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Already publicly imports RealCurve; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Transitive interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Transitive interface unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive interface unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive interface unchanged; no adaptation. |
| TargetsCheck | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive interface unchanged; no adaptation. |

## Status

landed 20261025T201954-L-2658788 2026-10-25 (merge of deliver/F8/Sheaf.DeligneLaumon.PairEigenvalueGeometricConstituent)
