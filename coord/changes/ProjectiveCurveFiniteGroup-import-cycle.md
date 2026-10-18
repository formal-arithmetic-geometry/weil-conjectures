# Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup import edge

## Reason

The returned delivery exposed an import cycle through the proof-only import of
`Sheaf.AlgebraicGeometry.ProjectiveCurveConstant` in this module. The item imports
the source `ProjectiveCurve` theorem, whose transitive imports reach this module
through `ProjectiveLineConstructible`. The imported wrapper declaration is not
used by the current theorem body. Removing the edge is therefore a forced
adaptation needed to compile the delivered item.

## Old

```lean
import Sheaf.AlgebraicGeometry.ProjectiveCurveConstant
```

## New

The import line is removed. Every declaration, theorem signature, visibility,
and proof body in the adapted module is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Its existing import of this module now compiles without the cycle. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | Its transitive import chain no longer reaches the item through a cycle. |

## Status

landed 20261018T091405-L-3256112 2026-10-18 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ProjectiveCurveConstant)
