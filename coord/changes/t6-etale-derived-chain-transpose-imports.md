# Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose imports

## Reason

The completed proof uses the already constructed canonical derived adjunction and
its Mathlib counit factorization. The old resolution-construction imports are
unnecessary. In particular, the three public imports below contribute no symbol
needed to state this module's theorem: the remaining public imports supply its
categories, functors, comparisons and instances. Removing these unused public
imports changes the transitive exported import interface, so this record makes
that interface cleanup explicit. No declaration signature, definition or instance
is changed. No module is withdrawn.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Basic
```

## New

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose --uses
etaleDerivedChainTranspose` reports no downstream modules. A source search also
finds no Lean importer of this module and no external use of its public theorem.
The DAG attachment and dependencies of unfinished parents remain intact; the
module is retained with its original public theorem signature and completed proof.
There are no forced adaptations and no target statement or definition changes.
The module's own single-file compile passed with the reduced import interface.

## Status

landed 20261021T120602-L-3914448 2026-10-21 (merge of deliver/T6/Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose)
