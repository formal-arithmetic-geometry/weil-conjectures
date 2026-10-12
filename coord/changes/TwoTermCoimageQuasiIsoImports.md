# CochainComplex.twoTermCoimage_quasiIso imports

## Reason
The proof uses no canonical truncation construction. Import the single-complex
and quasi-isomorphism interfaces required by the theorem signature directly,
instead of exporting the broader embedding/truncation module. The explicit
ShortComplex.HomologicalComplex import is redundant through QuasiIso.
No declaration's signature or definition changes.

## Old
```lean
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
```

## New
```lean
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.QuasiIso
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.UpperTruncationStepSES | unclaimed at review | No statement, definition, or proof change: it directly imports both removed modules already. |

The sole direct importer was identified by rg over lean/ for public and plain
imports of Sheaf.Algebra.Homology.TwoTermCoimageQuasiIso. Its two Mathlib public
imports are exactly the old block above, so the entire old exported environment
remains available to it and its downstream users. No forced adaptation is needed.
No target meaning changes, since no statement or data construction is altered.

## Status
landed 20261012T223358-L-1634402 2026-10-12 (merge of deliver/B2/Sheaf.Algebra.Homology.TwoTermCoimageQuasiIso)
