# AlgebraicGeometry.Scheme.Modules.IsAmple.exists_immersion_affine_base

## Reason

The proved private helpers use the limits and monoidal-category notation and names.
The static interface check classifies a changed `open` command as an interface change,
so this record documents the command change. Namespace openings are lexical to this
file and are not exported to importers. Every existing elaborated declaration type,
definition and public import remains unchanged. No target meaning changes.

## Old

```lean
open CategoryTheory
```

## New

```lean
open CategoryTheory Limits MonoidalCategory
```

## Users

The prescribed downstream scan reports 191 transitive importers, and two modules which
textually use the existing theorem name. Those two are listed below. All transitive
importers retain the same declaration type and public imports; the proof-only module
imports and the additional namespace openings do not alter their name resolution.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase | C1 | Proof scope expanded; existing theorem type unchanged. |
| Sheaf.AlgebraicGeometry.DimOneQuasiProjective | No claim in this checkout | No adaptation: existing theorem name and type unchanged. |

The new statement modules `Sheaf.AlgebraicGeometry.AmpleFinitePowerCover` and
`Sheaf.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso` have no prior users and are
imported only for the proof of this item. Their statements are recorded by the new nodes.

## Status

landed 20261012T070530-L-3467643 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.AmpleImmersionAffineBase)
