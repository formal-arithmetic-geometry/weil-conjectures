# AlgebraicGeometry.Etale.tailOpenCompatibleBoundaries

## Reason

The proof uses an irreducible fixed-boundary API and local definitions for
the constructed boundary values. Local transparency settings prevent elaboration from
expanding the inverse-image and cohomology map implementations during assembly.
The static interface checker records changes to these commands even though the
attributes are local. The existing theorem signature and public imports are
identical, and no existing definition is changed.

## Old

```lean
attribute [local irreducible] upperStar cohomologyMap
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree

set_option backward.isDefEq.respectTransparency true
```

## New

```lean
attribute [local irreducible] upperStar cohomologyMap
  openCohomologyRestriction openSquareCoefficient
  Sheaf.H.map

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The supplied difference in the new exactness API is an ordinary function with
its actual restriction-difference value formula. Boundary data is still the
explicit fixed homology connecting map. The local facts use inferred types to avoid redundant conversions
of cohomology instances while verifying the assembly. No data is chosen
from an unproved existence assertion.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleLimitOpenCompatibleBoundaries | S3 | Local elaboration commands and proof-only imports; signature and public imports unchanged. |

The changed commands have no downstream effect; no module needs adaptation.

## Status

landed 20261014T025142-L-158134 2026-10-14 (merge of deliver/S3/Sheaf.AlgebraicGeometry.EtaleLimitOpenCompatibleBoundaries)
