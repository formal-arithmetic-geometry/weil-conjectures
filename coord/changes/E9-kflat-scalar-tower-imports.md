# SheafOfModules.KFlatScalarTower public imports

## Reason

The proof and the statement use the fixed presentations and normalization, which
already expose the required scalar-extension definitions. They do not use the
cochain-model existence theorem or the cochain monoidal instances. Remove these
two unused public imports after proving the item.

## Old

```lean
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Functor.OfSequence
```

## New

```lean
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Mathlib.CategoryTheory.Functor.OfSequence
```

## Users

`tools/downstream.py` lists precisely one downstream module. No statement or
definition changes, and no target needs a mathematical statement review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TwoTermReductionCohomology | unclaimed | Imports both removed modules directly; no declaration from this item is referenced. No adaptation required. |

## Status

landed 20261021T111045-L-3980688 2026-10-21 (merge of deliver/E9/Sheaf.Algebra.Homology.KFlatScalarTowerRealization)
