# Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage public imports

## Reason

The statement uses arbitrary ring sheaves and the canonical module adjunction.
Importing finite-coefficient direct images unnecessarily exposes unrelated declarations
and adds proof dependencies. Import the canonical adjunction directly instead.
No declaration signature or visibility changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage --uses
proEtaleRingModule_closed_essImage_iff_and_unit_isIso` lists two downstream modules;
the only textual occurrence of the theorem name is its declaration. Neither downstream
module needs adaptation. Both originals are checked with lcompile.py against the new item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage | T7 | proof completed; public import narrowed |
| Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle | not adapted | unchanged; compile checked |
| Sheaf.AlgebraicGeometry.PurSupportExact | not adapted | unchanged; compile checked |

No target statement or definition is changed; no target meaning review is reopened.

## Status

landed 20261018T145117-L-3645885 2026-10-18 (merge of deliver/T7/Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage)
