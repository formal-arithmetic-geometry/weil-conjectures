# Sheaf.CategoryTheory.UnnormalizedPairFunctorDescent imports

## Reason

The theorem uses only general unnormalized stage systems and their morphisms.
The public exact-stage datum import is unused: the source Morphism module already
publicly imports StageSystem.Basic. Removing the unused dependency implements the
stage-3 pruning requirement without changing any declaration or its type.

## Old

```lean
public import Sheaf.CategoryTheory.ExactStagePairData
public import WeilConjectures.CategoryTheory.StageSystem.Functor
```

## New

```lean
public import WeilConjectures.CategoryTheory.StageSystem.Functor
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.UnnormalizedPairFunctorDescent | F4 | Own statement and proof use only the retained Morphism import. |

There are no current direct Lean importers of the item, checked by rg and an exact
import-line scan over lean/. The planned parent node
`lem-pur-general-pair-shift-normalization` has no Lean attachment. Its mathematical
use of the proved theorem is unchanged. No target statement or definition changes.
The general pair-data definition node remains a dependency; its module is not withdrawn.

## Status

landed 20261027T094403-L-221514 2026-10-27 (merge of deliver/F4/Sheaf.CategoryTheory.UnnormalizedPairFunctorDescent)
