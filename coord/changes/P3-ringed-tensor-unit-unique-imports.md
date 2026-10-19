# SheafOfModules.canonicalRingedTensorComparison_unit_unique

## Reason

The module's statement and its formal monoidal uniqueness proof need only the tensor comparison data module. Remove the unused public homological imports and redundant imports. This also avoids an import collision between the legacy WeilConjectures TensorClosed and Sheaf TensorClosed declarations in the current compile environment. No declaration, definition, universe, binder, visibility or theorem statement changes.

## Old

Public imports, verbatim:

```lean
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.CategoryTheory.Adjunction.Limits
```

## New

Public imports:

```lean
public import Sheaf.Paper.RingedTopoiTensorComparisonData
```

The theorem signature is unchanged verbatim. Its proof now uses cancellation, tensor functoriality and tensor_left_iff.

## Users

`tools/downstream.py --direct` reports one direct importer. `tools/downstream.py --uses canonicalRingedTensorComparison_unit_unique` reports the parent and the item itself as the only textual declaration users. There are 1909 transitive import descendants, but the parent's import of the item is private; changes to this module's public imports do not propagate through it to those descendants. The parent's own explicit imports already contain all thirteen removed modules, with identical public/private visibility to the item's original imports. Therefore all consumers keep the same declarations available and their statements have the same meaning. No target definition changes and no target statement review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | unclaimed | Sole direct importer and external theorem user. Independently imports every removed module; no adaptation required. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitUnique | P3 | Proof completed, imports pruned; signature unchanged. |

## Status

landed 20261019T192814-L-1870294 2026-10-19 (merge of deliver/P3/Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitUnique)
