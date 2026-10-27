# CategoryTheory.TowerRightDerivedEvaluation.exists_normalized proof context

## Reason

The proof introduces three standard backward-elaboration options to elaborate the
canonical functor and localization comparisons. The static command checker requires
a change record for these added commands. These options affect elaboration in this
file only. They do not export an instance or notation, and do not change the types
of the public declarations or the body of the public definition `cochainUnit`.
No target meaning changes.

## Old

After `cochainUnit`, no elaboration-option commands occurred before the theorem.
The existing option was:

```lean
set_option autoImplicit false
```

## New

The existing auto-implicit setting is preserved. After `cochainUnit`, add:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

All new helper declarations are private and fully proved or real natural-transformation
constructions. The existing public definition and theorem signature remain verbatim.
The proof also removes the unused private imports of
`Sheaf.CategoryTheory.KInjectiveExactSquareComparison` and
`Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`; all public imports stay unchanged.

## Users

`tools/downstream.py Sheaf.CategoryTheory.TowerRightDerivedEvaluation --uses` for
both public declaration names finds zero downstream modules; each name occurs only
in the item itself. Direct textual searches of both Lean roots agree. The DAG's
unfinished parents may still use the unchanged theorem, so the item is retained.
No consumer adaptation is necessary and no other group's module is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.TowerRightDerivedEvaluation | C6 | Proof completed; local elaboration options only; unchanged public signatures and definition. |

## Status

landed 20261022T143024-L-925793 2026-10-22 (merge of deliver/C6/Sheaf.CategoryTheory.TowerRightDerivedEvaluation)
