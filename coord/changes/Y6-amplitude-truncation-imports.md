# Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison public imports

## Reason

The proof uses the standard derived t-structure and the source library's proved
coproduct and homology lemmas. The broad truncation/homotopy-colimit module supplies
many unrelated constructions and proof dependencies. Replace it by the precise
Mathlib module needed by the unchanged public theorem statement.

## Old

```lean
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
```

## New

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
```

All other public imports and the complete existing theorem signature are unchanged.
The three new proof imports are private. No source-library file changes.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison
--uses DerivedCategory.amplitude_truncation_family_comparison` reported zero
current downstream modules. A direct import search agreed. The item remains
attached to its existing DAG node and is proved, not withdrawn; its parents with
unfinished proofs keep the same statement and all names used by that statement
remain public. There are no consumers requiring adaptations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison | Y6 | Proves the same theorem; replaces an unused broad public import by the needed Mathlib import. |

## Status

landed 20261021T121009-L-4036791 2026-10-21 (merge of deliver/Y6/Sheaf.CategoryTheory.AmplitudeTruncationFamilyComparison)
