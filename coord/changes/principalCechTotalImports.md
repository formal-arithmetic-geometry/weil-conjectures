# PrincipalOpenCechTotal imports and elaboration options

## Reason

The module never uses the scheme-derived-category declarations of
`Sheaf.AlgebraicGeometry.DerivedCategory`; the remaining imports supply all generic
derived-category declarations in the existing signatures. The second reader
verified a clean scratch compile without it and removed this unused public import.

The completed proofs never use sorted finite subsets, so remove the unused public
`Mathlib.Data.Finset.Sort` import. The module's own clean file compile verifies that
its statements and definitions still elaborate. This removes an exported import,
so the static preflight requires this record and independent review.

The added transparency option supports proof elaboration across the two existing,
definitionally equal presentations of scheme modules. The local linter option
preserves the existing unused binder `hC` verbatim after filling the functor proof.
Neither option changes an exported declaration's type or mathematical meaning.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Data.Finset.Sort
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

set_option backward.isDefEq.respectTransparency false
```

The existing `principalCechFunctor_exists` theorem had no declaration-local
`linter.unusedVariables` setting.

## New

```lean
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The existing `principalCechFunctor_exists` theorem is preceded by
`set_option linter.unusedVariables false in`. Its signature is unchanged.
All existing definitions and statements of the module are unchanged.

## Users

`tools/downstream.py ... --uses principalCechFunctor_exists` reports only the item's
own module as a textual user of this declaration. The four direct importers are
listed below; the import graph has 362 transitive downstream modules. Their types
and mathematical meaning are unchanged because no definition, instance interface,
or theorem signature changed. No downstream adaptations are included. The global
build must verify the exported-import removal for the whole closure.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal | E1 | Seven theorem proofs filled; two unused imports removed |
| Sheaf.AlgebraicGeometry.PrincipalCechResolutionQuasiIso | unclaimed in local claim records | Same Cech interface; no edit |
| Sheaf.AlgebraicGeometry.PrincipalCechFiniteColumnModel | unclaimed in local claim records | Same Cech interface; no edit |
| Sheaf.AlgebraicGeometry.PrincipalOpenSectionsResolutionQuasiIso | unclaimed in local claim records | Same sections interface; no edit |
| Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction | unclaimed in local claim records | Same Cech interface; no edit |

No target definition changes, so target statement review is not reopened.

## Status

landed 20261013T054212-L-441651 2026-10-13 (merge of deliver/E1/Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal)
