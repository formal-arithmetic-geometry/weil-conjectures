# AlgebraicGeometry.exists_isIso_limitProjection_of_isClosedImmersion_of_locallyOfFinitePresentation

## Reason

The proof uses the given limit and Mathlib's restriction of limiting cones. It does not use
construction of a limit or any declaration of `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
Remove the unused public import to prune that dependency. The theorem signature is unchanged.
This record documents the public-import removal only; no definition or statement changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
```

## New

The line is removed. The proof-only import supplying the restriction and descent API is:

```lean
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
```

## Users

`tools/downstream.py` lists the following eight downstream modules. None mentions any
of the declarations from the removed public import. The direct importer is compiled
unchanged against the pruned interface. No adaptation is made to another group's file.
The theorem's type and all definitions used by targets retain their meanings.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | H5 | No declaration from the removed import is used; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | U2 | No declaration from the removed import is used; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | M3 | No declaration from the removed import is used; statement unchanged. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | C6 | No declaration from the removed import is used; statement unchanged. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | D9 | No declaration from the removed import is used; statement unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization | E6 | No declaration from the removed import is used; statement unchanged. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | R5 | No declaration from the removed import is used; statement unchanged. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | W3 | No declaration from the removed import is used; statement unchanged. |

## Status

landed 20261018T062802-L-652869 2026-10-18 (merge of deliver/G9/Sheaf.AlgebraicGeometry.ClosedLimitLfpStabilization)
