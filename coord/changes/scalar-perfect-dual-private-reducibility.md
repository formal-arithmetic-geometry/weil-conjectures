# CategoryTheory.ScalarPerfectDual private proof helpers

## Reason

Stage-3 preflight classifies the added local attribute command as changing what other
modules see and requires this record. The command prevents elaboration of the main
finite-free retract proof from unfolding already-proved unit and finite-product
isomorphisms. The final module compiles in 52.0 seconds with the prescribed 60-second
limit. No existing signature, definition, public import or public attribute changes.

## Old

No private helper declarations or corresponding reducibility command occurred between
`unitComplex` and `scalarPerfectDualRealization`.

## New

The delivery adds fully proved private helpers `constantUnitIso`, `extension`,
`extensionUnitIso`, `realizationUnitIso`, `finiteFreeIso`, and `productFreeIso` and then:

```lean
attribute [local irreducible] constantUnitIso extension extensionUnitIso realizationUnitIso
  finiteFreeIso productFreeIso
```

The attribute is local to this file and applies only to new private helpers. One helper
also uses a declaration-local `backward.isDefEq.respectTransparency.types false` option.
Every existing public declaration header and non-theorem definition is unchanged.
There is no mathematical interface change and no target needs statement review.

## Users

`tools/downstream.py Sheaf.Paper.ScalarPerfectDualRealization --uses
CategoryTheory.ScalarPerfectDual.scalarPerfectDualRealization` reports zero downstream
modules and one use in the item itself. A repository-wide Lean import search also finds
no current importers. The parent DAG node remains attached and is not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarPerfectDualRealization | X7 | Private proof elaboration only; seven theorem bodies filled. |

## Status

landed 20261021T151208-L-1177310 2026-10-21 (merge of deliver/X7/Sheaf.Paper.ScalarPerfectDualRealization)
