# DerivedInjectiveConeComparison transparency options

## Reason

The proof requires Mathlib's backward elaboration through the full-subcategory
inclusion and quotient factorization. The module-scope options make the existing
proof elaborate within the file's compile budget.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Abelian.DerivedInjectiveConeComparison | S7 | Compiles against the unchanged public declarations; importers see only the existing declarations and signatures. |

## Status

landed 20261023T124415-L-1395779 2026-10-23 (merge of deliver/S7/Sheaf.CategoryTheory.Abelian.DerivedInjectiveConeComparison)
