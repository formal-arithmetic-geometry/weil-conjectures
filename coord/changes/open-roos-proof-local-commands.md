# WeilConjectures.OpenRoos.openRoosUnitAdjunction

## Reason

The completed proof adds private generic helpers. Their universe parameters and a scoped
`SheafOfModules` opening are visible to the static command comparison, which requires
this record. Every existing declaration signature, definition body and public import is
unchanged. The record documents proof support; it changes no mathematical interface.

## Old

The original module declares:

```lean
universe t u
```

It has no `LocalUnit` section or opening of `SheafOfModules` around these new helpers.

## New

```lean
universe t u c v r
```

The added proved private local-unit helpers are enclosed by these commands:

```lean
section LocalUnit
open SheafOfModules
-- proved private helpers
end LocalUnit
```

Several new private helpers also use declaration-local commands:

```lean
open Classical in
set_option backward.isDefEq.respectTransparency false in
```

The extra universes belong to private helpers. The opening is scoped and closes before
existing public declarations. No instance, notation or attribute is added. In particular
all seven existing definitions and the complete theorem signature remain byte-identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | T5 | Private proof support; original public API unchanged. |

No library module currently imports this item or refers to its theorem; its unfinished
parent still cites its DAG node. No consumer adaptation is needed. The preserved node
attachment and parent route remain in place. Target statements and their definitions are
unchanged, so no target-meaning review is reopened by these commands.

## Status

landed 20261021T214857-L-1877183 2026-10-21 (merge of deliver/T5/Sheaf.SixFunctors.OpenRoosUnitAdjunction)
