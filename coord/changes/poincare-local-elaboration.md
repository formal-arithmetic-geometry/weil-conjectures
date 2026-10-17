# WeilConjectures.PoincareDuality.Poincare local elaboration attributes

## Reason

The retained proof elaboration avoids expanding the K-injective internal-Hom structure
and the coefficient pullback construction. Prefer the full-subcategory monoidal
instance locally so that typeclass search uses the existing structure directly.
These commands have local scope: none is exported to an importing module. The
preflight conservatively classifies commands outside declaration bodies as interface
changes and requests this record. No existing public declaration, definition body,
public import, theorem signature or global attribute changes.

## Old

No local attribute commands at the start of the public section.

## New

```lean
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local instance 2000] CategoryTheory.ObjectProperty.fullMonoidalSubcategory
```

The trace-cup proof now supplies its four abstract arguments explicitly. The isomorphism
proof first proves the generic composition-of-isomorphisms assertion in a private,
fully proved helper, then instantiates it with the existing Verdier exchange theorem.
The source module also imports the two proved Sheaf helper modules privately and proves
the shifted zero-twist case in a private theorem. No arbitrary data is chosen.

## Users

Source-only audit:
`python3 tools/downstream.py WeilConjectures.PoincareDuality.Poincare --uses
AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived`.
The only declaration-level use is the wrapper in the item itself.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.PoincareDuality.Poincare | G3 | Local elaboration only; same public signatures and definition bodies. |
| TargetsCheck | unclaimed | Imports the same public API; local attributes are not exported. |
| WeilConjectures | unclaimed | Imports the same public API; local attributes are not exported. |

No consumer adaptation is needed. No target changes its meaning, and no target semantic
review is reopened by these local commands.

## Status

landed 20261017T131009-L-1769097 2026-10-17 (merge of deliver/G3/WeilConjectures.PoincareDuality.Poincare)
