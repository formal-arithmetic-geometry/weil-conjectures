# DerivedCategory.torAmplitudeIn_of_principal_cover import interface

## Reason

The theorem is now proved entirely with ordinary module K-flat models. The sheaf-site
change-of-rings theorem is not used, so its public re-export is removed. No existing declaration,
statement, definition, universe, or visibility changes. The file also opens
`MonoidalCategory` for the new proof notation and adds a proved private helper; neither
changes an existing public declaration. No target meaning changes.

## Old

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
```

## New

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PerfectPrincipalCoverGlue | unclaimed in the queue at inspection | The only direct importer; it already imports DerivedChangeOfRings independently. Its declarations and instances remain available. No adaptation required. |

The downstream declaration search found no consumer mentioning
`torAmplitudeIn_of_principal_cover` yet: the parent proof remains a sorry.

## Status

landed 20261018T062820-L-659395 2026-10-18 (merge of deliver/K2/Sheaf.Algebra.Homology.TorAmplitudePrincipalCover)
