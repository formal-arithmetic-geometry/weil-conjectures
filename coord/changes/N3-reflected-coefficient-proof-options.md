# Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares proof elaboration options

## Reason

The proofs compare morphisms whose object types unfold the completion, the
full-subcategory inclusion and its lift. Elaborating the reflection and mate
calculations requires the standard backward-defeq settings used in the imported
Mathlib category-theory modules. Preflight classifies additional commands as
an interface change and requests this record. These options affect proof
elaboration only; every original declaration header and data body is unchanged.
All new helpers are private and fully proved. No consumer adaptation is required.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares`
reports zero downstream modules in the current library. Unfinished DAG parents
remain attached; no node or module is withdrawn. All original public declarations
retain their exact signatures, and all original definitions and instances retain
their bodies, so consumers and target meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares | N3 | Proof elaboration only; 18 holes closed, zero added. |

## Status

landed 20261021T130102-L-2519811 2026-10-21 (merge of deliver/N3/Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares)
