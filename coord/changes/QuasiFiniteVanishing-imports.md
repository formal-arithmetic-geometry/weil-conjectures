# WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing import visibility

## Reason

Quasi-finite factorization and lower-shriek functoriality are used only in proofs in this
module. They must be plain imports. The lower-shriek definitions used by its unchanged
statements are imported publicly from the narrower definitions module. This changes import
visibility, not any theorem statement or definition. The original QuasiFiniteStalk, FiniteMap, and FibreCohomology modules fail against this
change because their proofs used previously reexported functoriality isomorphisms. Each
forced adaptation adds exactly one plain proof import.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
```

Each forced adaptation adds this line, preserving every declaration:

```lean
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
```

## Users

The table below lists all modules found by `tools/downstream.py` on the shared repository.
No declaration statement or definition changes in any user. Direct consumers and references
to the removed reexports are checked against the revised sandbox modules; the three adapted
modules each add their own proof import. No target statement needs renewed semantic review.

| module | group holding it | effect |
| --- | --- | --- |
| Comparator.Weil.Solution | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures | unclaimed | Original compiles; its other public imports retain both reexports. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Forced adaptation: one plain functoriality proof import; every declaration unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Forced adaptation: one plain functoriality proof import; every declaration unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Original compiles; its other public imports retain both reexports. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Forced adaptation: one plain functoriality proof import; every declaration unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.Statement | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Unused reexports disappear; no use of the removed named project results; declarations unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Its other public imports retain the reexports; declarations unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Its other public imports retain the reexports; declarations unchanged. |

The source-reference audit of lost project-module declarations found substantive uses only
in the three adapted modules. Other textual hits were unrelated `map` methods. Mathlib
module names in the conservative public-import graph audit are not themselves declaration
uses. The original direct consumers FormalSteps and the WeilConjectures umbrella compile.
Each original adapted module was compiled against the changed dependencies and failed with
the exact missing isomorphisms listed in the report; each revised module adds only the needed
proof import. No theorem or definition is replaced or reinterpreted.

## Status

landed 20261015T194212-L-1174801 2026-10-15 (merge of deliver/E3/WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing)
