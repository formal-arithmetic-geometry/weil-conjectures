# CategoryTheory.sfbSectionActionInternal proof scopes

## Reason

The complete proof needs the canonical self-enrichment scope to instantiate the presheaf
enriched Homs. Private product helpers also use a locally declared coefficient sheaf B.
The static preflight requests a change record for these scope/variable commands, even
though no existing declaration signature or definition body changes. The helper
`underlyingModule` merely exposes `M.obj.mod` under the definition
`sfbSectionUnderlying`; its instance registration is explicitly local to this module.

## Old

```lean
open scoped TensorProduct
```

No private product-helper coefficient variable or underlying-module helper existed.

## New

```lean
open scoped TensorProduct CategoryTheory.MonoidalClosed

@[instance_reducible] private def underlyingModule
    {B' : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [MonObj B']
    (M : sfbSectionModules J B') : ModObj B' (sfbSectionUnderlying J M).obj := M.obj.mod

attribute [local instance] underlyingModule

variable {B : Sheaf J CommRingCat.{w}}
```

The extra variable only supplies a binder in the new private product helpers; the existing
main theorem continues to bind its own B. All old declarations keep their signatures,
visibility, attributes and data definitions. Only theorem proofs are filled; no target
meaning changes. There is no new public instance or declaration.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SectionActionInternal --uses
sfbSectionActionInternal` reports zero downstream modules and only the item's own use.
An `rg` search of both Lean roots for the module and all sfbSection names likewise finds
only the item. Parent DAG citations and the unit route remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SectionActionInternal | S4 | Proof helpers and local elaboration scopes; all existing interfaces unchanged. |

No consumer adaptations are needed. No file under the adopted source root is changed.

## Status

landed 20261023T124320-L-1370620 2026-10-23 (merge of deliver/S4/Sheaf.CategoryTheory.SectionActionInternal)
