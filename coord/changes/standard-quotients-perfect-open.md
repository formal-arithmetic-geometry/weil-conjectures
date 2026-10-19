# Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect module scope

## Reason

The implemented two term resolution uses the `HomologicalComplex` namespace
for Mathlib's `double` construction and its API. The proof therefore adds that
namespace to the module's existing `open` command.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

## New

```lean
open CategoryTheory CategoryTheory.Limits HomologicalComplex
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect | H4 | Uses the namespace-qualified Mathlib resolution API in its proof. |

## Status

landed 20261019T005303-L-2748398 2026-10-19 (merge of deliver/H4/Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect)
