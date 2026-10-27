# CategoryTheory.pointSystemRefine

## Reason

Restore the completed M3 proof from commit 4993207a069, as requested by the
2026-10-25 restoration handoff in coord/returns/Y3.md. The earlier batch take-out
was caused by an unrelated missing module. The restored proof uses elementwise
filtered colimits and finite common upper bounds instead of the general
filtered-colimit/finite-limit comparison. Its statement is unchanged.

## Old

```lean
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
```

## New

```lean
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
```

The other two public imports and the entire existing theorem signature remain
unchanged. The new index, diagrams, instances, and proved helpers are private.
The unused `set_option warn.sorry false` is also removed. No target definition
or statement changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointSystemRefine | Y3 | Restore its complete proof and narrow imports. |
| Sheaf.CategoryTheory.PointSystemRefineAll | unchanged consumer; no adaptation | Its private import of the item is its only direct import edge; its application uses the unchanged theorem signature. |

This is the complete direct-consumer and direct-use output of
`tools/downstream.py Sheaf.Paper.PointSystemRefine --direct --uses pointSystemRefine`.
The direct consumer imports the item privately, so the replaced public import is
not re-exported through that edge. All other downstream paths pass through this
consumer. No consumer requires modification.

## Status

landed 20261025T071248-L-169333 2026-10-25 (merge of deliver/Y3/Sheaf.Paper.PointSystemRefine)
