# AlgebraicGeometry.perfect_hom_open_test_bijective

## Reason

The theorem uses only `perfectHomComposition` from `PerfectHomTransport`, not the
representing cocone constructed in `PerfectHomPushPullCocone`. Prune the latter
public import while retaining the necessary statement declarations. Add the
new geometric mate theorem and the projection adjunction existence theorem as
proof-only imports. No statement or definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
```

## New

```lean
public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.PerfectHomOpenComparisonMateIso
```

## Users

`tools/downstream.py --uses AlgebraicGeometry.perfect_hom_open_test_bijective`
finds one other module mentioning the theorem. There is one direct importer.
Its public `PerfectHomOpenRestrictedEquivFields` dependency already imports the
representing-cocone data, so it still receives all declarations needed by its
signature. The theorem's elaborated type is identical. No adaptation is forced
or included; downstream statements and definitions retain their meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectHomOpenTestBijective | V1 | Proof and imports changed; signature identical. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps | Not adapted | Calls the unchanged theorem; obtains cocone data from its existing public dependency. |

## Status

landed 20261014T022552-L-4047894 2026-10-14 (merge of deliver/V1/Sheaf.AlgebraicGeometry.PerfectHomOpenTestBijective)
