# SheafOfModules.exists_scalarDualEvaluationDescent

## Reason

The direct tensor and internal-Hom proof needs the existing change-of-rings tensor
notation and permits elaboration across the canonical coefficient-ring transports.
Preflight conservatively classifies the added commands as a visible-context change.
All existing public declaration signatures and definition bodies remain verbatim.
The local-surjectivity instance is introduced with `have` inside `scalarOver_ext`;
no new global instance is registered.

## Old

```lean
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
```

## New

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open scoped ChangeOfRings
```

These commands enable notation and elaboration in this module. They do not alter
the types or values of existing public definitions, and add no hypothesis or axiom.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent | B6 | The proof elaborates across coefficient transports; existing public declarations are identical. |

A textual search of the current library finds no other module importing this item
or using its six public declaration names. Unfinished DAG parents still need this
item, so it is retained and proved. No consumer adaptation is required.

## Status

landed 20261023T102427-L-2898169 2026-10-23 (merge of deliver/B6/Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent)
