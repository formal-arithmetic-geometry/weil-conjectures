# WeilConjectures.WeilSheaf.Finiteness public imports

## Reason

The general constant-coefficient compact-support bound is reduced to finite coefficients and
an integral/rational coefficient comparison. It does not use smooth proper Poincare duality.
Removing that public import makes this independence explicit. Four other direct public imports
are redundant: their declarations remain public through retained imports. No existing theorem
signature, definition, universe or visibility changes. No target statement changes.

The original proof of `WeilSheaf.IsUnitCompatible.lowerStar` timed out at the 60-second limit.
Its unchanged statement is now proved by the existing `lowerStar_unit_str` lemma, imported
privately from `WeilSheaf.LowerStarPairing`; the whole module compiles in under ten seconds.

## Old

```lean
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.PoincareDuality
public import WeilConjectures.WeilSheaf.ProperCohomology
public import WeilConjectures.WeilSheaf.StalkPairing
```

The forced original line in `TraceFormula` was:

```lean
    have := WeilSheaf.subsingleton_cohomology_adicConstant k₀ l X d hi'
```

## New

```lean
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.ProperCohomology
import WeilConjectures.WeilSheaf.LowerStarPairing
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension
import Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison
```

The first two original public imports (geometric connectedness and constant global sections)
are retained verbatim and are omitted from both excerpts above.

`TraceFormula` gains only the private import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` and a proof that the geometric fibre
has dimension at most `d`, obtained from smooth relative dimension and its base-change instance.
The replaced line is then:

```lean
    have := WeilSheaf.subsingleton_cohomology_adicConstant_of_isProper k₀ l X d he i hi'
```

## Users

The source-only `downstream.py WeilConjectures.WeilSheaf.Finiteness --uses
subsingleton_cohomology_adicConstant poincareDuality` finds 57 downstream modules. Their current
claim holders and effects follow. Only `TraceFormula` is adapted, and it is unclaimed.
`PoincareDuality` itself is held by F3 and is not edited.

| module | group holding it | effect |
| --- | --- | --- |
| `WeilConjectures` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.Statement` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Duality is supplied independently through Weights; no adaptation. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Duality is supplied independently through Weights; no adaptation. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Duality is supplied independently through Weights; no adaptation. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | Forced proof adaptation: use the proper dimension-bound theorem; add its smooth-dimension proof import. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No statement or definition changed; imports remain available through retained imports. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Already imports PoincareDuality directly; no adaptation. |

The five downstream modules mentioning a removed duality declaration are `TraceFormula`,
`BettiSymmetry`, `DualityReciprocity`, `SmoothProper` and `Weights`. The latter four retain their
independent public path to `PoincareDuality` through `Weights` (which imports it directly).
The direct importers of Finiteness are checked against the sandbox overlay separately.

## Status

landed 20261015T191323-L-1006997 2026-10-15 (merge of deliver/F1/WeilConjectures.WeilSheaf.Finiteness)
