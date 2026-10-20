# CategoryTheory.RingedCoefficientCounit.ringedCoefficientRestrictionCounit

## Reason

The complete representative proof needs controlled elaboration of the large presentation
structures. Set both backward definitional-equality transparency options to true by default,
and use local false settings on the private ordinary/representative calculations that need
unfolding. This changes only elaboration settings, not any mathematical definition, theorem
signature, universe, binder or visibility. The three direct consumers import this module
but do not mention the theorem by name.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The original public theorem signature is byte-for-byte unchanged. Private proved helpers
use scoped settings and `omit` commands; they add no public interface. The original variable,
universe, namespace and section declarations are preserved.

## Users

`tools/downstream.py Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
--uses ringedCoefficientRestrictionCounit` lists the following 38 downstream modules and
finds no use of the declaration outside its own module. No existing declaration changes type.
Options are local to elaboration of this file and do not change importing modules' settings.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.NearbyCycleSheafFiniteness` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.NearbyProperHyperdescent` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | V8 | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.OrgogozoGoodModification` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.PsiGoodOrientedCohomologyStrata` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.TraitNearbyBaseChange` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.WeilOne` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | J7 | No signature or visibility change; no adaptation needed. |
| `Sheaf.TraceFormula.BoundedConstructibleTransport` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` | unclaimed | No signature or visibility change; no adaptation needed. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | No signature or visibility change; no adaptation needed. |
| `TargetsCheck` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.Statement` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No signature or visibility change; no adaptation needed. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | No signature or visibility change; no adaptation needed. |

## Status

landed 20261020T051148-L-1582392 2026-10-20 (merge of deliver/D7/Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit)
