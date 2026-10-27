# AlgebraicGeometry.ProEtale.CondensedRing.uncurry_poincareMap_of_smooth

## Reason

Restore the current quarantine archive and close its proof using the existing
upstream theorem. Drop redundant imports of independent target wrappers and
already available category APIs. No declaration signature, definition, or target
meaning changes. The upstream Poincare source and its public imports are untouched.

## Old

Archived imports:
```lean
public import WeilConjectures.PoincareDuality.Poincare
public import Sheaf.Targets.SmoothPurityQbar
public import Sheaf.Targets.PoincareTateBoundedConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Category
```
The theorem's archived proof was `sorry`.

## New

```lean
public import WeilConjectures.PoincareDuality.Poincare
```
The theorem's signature is verbatim from the archive; its proof is:
```lean
by
  exact Verdier.uncurry_poincareMap
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (boundedConstructibleExceptionalProjection _ ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)
```

## Users

`python3 tools/downstream.py Sheaf.Targets.PoincareUncurry --uses
AlgebraicGeometry.ProEtale.CondensedRing.uncurry_poincareMap_of_smooth` reports
`unknown module(s)` because the item is quarantined. A direct search of `lean/`
and `quarantine/` finds no importers and no uses of the wrapper declaration.
This is a restoration, not a withdrawal; its DAG attachment and all statement
dependencies are preserved. No consumer adaptation is needed, and no target
semantic review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Targets.PoincareUncurry | T1 | Restore archived statement; prove its theorem; prune redundant imports. |

## Status

landed 20261025T041245-L-1118031 2026-10-25 (merge of deliver/T1/Sheaf.Targets.PoincareUncurry)
