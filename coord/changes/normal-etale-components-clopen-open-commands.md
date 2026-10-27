# Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen open commands

## Reason

The private proof helpers transport universal cocones and therefore open
`CategoryTheory.Limits`. No declaration signature or public import changes.

## Old

```lean
open CategoryTheory
```

## New

```lean
open CategoryTheory

open CategoryTheory.Limits
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen
--uses normal_etale_components_clopen` lists the declaration in its own file and
its direct consumer. The complete downstream module list also includes
`Sheaf.AlgebraicGeometry.GeometricCoverComponentQcProper`.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen` | Q4 | Proof filled; signature unchanged. |
| `Sheaf.AlgebraicGeometry.NormalGeometricCoverComponents` | unclaimed | Unchanged consumer. |
| `Sheaf.AlgebraicGeometry.GeometricCoverComponentQcProper` | unclaimed | Unchanged consumer. |

## Status

landed 20261023T232007-L-3673293 2026-10-23 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.NormalEtaleComponentsClopen)
