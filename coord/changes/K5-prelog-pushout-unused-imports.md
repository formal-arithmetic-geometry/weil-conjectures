# Sheaf.AlgebraicGeometry.PrelogPushoutHomExtension public imports

## Reason

The extension proof uses the supplied universal property `hsh`; it needs neither
sheafification construction module. Remove these unused public imports. The item
has no direct Lean importers in the current source tree. Its own theorem statement,
universes and visibility are unchanged.

## Old

```lean
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
```

## New

Both import lines are removed. No declaration signature changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PrelogPushoutHomExtension | K5 | Uses hsh directly; compiles without both imports. |

There are no direct importing Lean modules to adapt or compile. DAG parents with
unfinished proofs retain this theorem, whose statement is unchanged.

## Status

landed 20261026T082403-L-2168311 2026-10-26 (merge of deliver/K5/Sheaf.AlgebraicGeometry.PrelogPushoutHomExtension)
