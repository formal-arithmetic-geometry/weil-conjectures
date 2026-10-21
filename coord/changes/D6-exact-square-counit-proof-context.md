# CategoryTheory.exactSquare_derived_counit

## Reason

The complete proof uses local instances for preservation of finite limits and colimits
by composition, and Lean's backward elaboration options for the termwise comparison
isomorphisms. Preflight requests a change record for these commands. All existing
public signatures, definitions, and public imports remain unchanged. No target changes.

## Old

The original file has no additional proof elaboration options or composition instances.
Its only configuration command is:

```lean
set_option autoImplicit false
```

## New

The original command is retained. These proof elaboration options and local attribute
are added before the private helpers:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

Two `omit [HasDerivedCategory A] in` commands keep unused section instances out of
private helper signatures. All helpers are proved private theorems. These commands
only affect elaboration within this file and expose no additional API to importers.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ExactSquareDerivedCounit | D6 | Complete proof; private helpers and local proof context only. |
| Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization | K1 | DAG parent; no current Lean use or adaptation. The existing theorem signature is identical. |

`tools/downstream.py Sheaf.CategoryTheory.ExactSquareDerivedCounit --uses
CategoryTheory.exactSquare_derived_counit` reports zero downstream modules and only
the item itself as a textual declaration use. No consumer needs adaptation;
none sees the local attributes or option values. No definitions used by targets change.

## Status

landed 20261021T111022-L-3913629 2026-10-21 (merge of deliver/D6/Sheaf.CategoryTheory.ExactSquareDerivedCounit)
