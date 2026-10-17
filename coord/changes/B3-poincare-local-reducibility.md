# Poincare module elaboration attributes

## Reason

The Poincare module exceeded the 60-second single-file compile limit because
kernel conversion unfolded the derived closed structure, coefficient module
closed structure, and pro-étale upper-star implementation. Module-local
irreducibility attributes stop those implementation bodies from unfolding while
this module elaborates. The local instance priority keeps the intended
bounded-constructible subcategory instance selected.

## Old

```lean
@[expose] public section

universe u
```

## New

```lean
@[expose] public section

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local instance 2000] CategoryTheory.ObjectProperty.fullMonoidalSubcategory

universe u
```

The attributes are local to this module and do not alter any declaration,
signature, theorem statement, definition, or public import.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.Poincare | B3 | The item compiles within the 60-second limit. |

## Status

landed 20261017T183135-L-1718844 2026-10-17 (merge of deliver/B3/WeilConjectures.PoincareDuality.Poincare)
