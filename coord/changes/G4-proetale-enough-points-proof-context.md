# AlgebraicGeometry.proEtale_enoughPoints proof context

## Reason

The proof uses category-theoretic limit notation and fully proved private helpers.
The static command checker requires a change record for expanding `open` and
adding a local instance priority and an explicit auto-implicit setting.
The public theorem's complete signature and both public imports stay unchanged.
No definitions are changed and no target's meaning changes.

The local priority selects the direct sheaf-colimit instance over general
full-subcategory closure search. It only affects elaboration in this module.
The new private import supplies the standard full-subcategory limit construction.

## Old

```lean
open CategoryTheory
```

No local instance priority or explicit auto-implicit command followed it.

## New

```lean
open CategoryTheory CategoryTheory.Limits

-- Use the direct sheaf colimits instead of searching through full-subcategory closure.
attribute [local instance 2000] Sheaf.instHasColimitsOfShape

set_option autoImplicit false
```

Each private helper also scopes
`set_option backward.isDefEq.respectTransparency false in` to its own proof.
All helper declarations are private proved theorems. These commands introduce
no exported notation, instance, definition, or public signature change.

## Users

The source scan finds no current Lean importers of this module and no use of
`proEtale_enoughPoints` outside its own declaration. This item remains needed
by its DAG parents, whose unfinished proofs will use its unchanged statement.
No consumer requires adaptation and no other group's module is modified.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints | G4 | Same public statement; proof completed. |

## Status

landed 20261020T162305-L-3587202 2026-10-20 (merge of deliver/G4/Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints)
