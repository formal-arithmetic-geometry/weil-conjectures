# DerivedCategory.isPerfectRingComplex_of_perfect_cohomology

## Reason

The proof uses the zero object of the category of cochain complexes and the canonical
triangle constructor. It adds two file-local opens. The delivery checker conservatively
classifies changes to open commands as an interface change and requests this record.
No existing declaration signature, visibility, definition, instance, notation, or attribute
changes. All new helpers are private and proved.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

## New

```lean
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CategoryTheory.Pretriangulated
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly
--uses isPerfectRingComplex_of_perfect_cohomology` reports one downstream module,
`Sheaf.Paper.CoefficientFrobenius`, and no external textual uses of the declaration yet.
Its import is proof-only; all five theorem signatures were inspected and are unaffected.
The public imports of the item are identical. The added opens only resolve names and
instances while elaborating this file; no target's meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly | Z8 | Proof completed; two opens added; existing signature unchanged. |
| Sheaf.Paper.CoefficientFrobenius | unclaimed | No source or statement change; no adaptation required. |

## Status

landed 20261018T135948-L-2974492 2026-10-18 (merge of deliver/Z8/Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly)
