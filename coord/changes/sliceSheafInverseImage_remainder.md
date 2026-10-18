# CategoryTheory.sliceSheafInverseImage_remainder

## Reason
The parent proof needs the finite-limit and restriction-comparison portion of the slice
adjunction as a separately named intermediate theorem.

## Old
No declaration.

## New
The declaration in `lean/Sheaf/CategoryTheory/Sites/SliceSheafInverseImageEquivalence.lean`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SliceSiteLocalization | P4 | imports and applies the intermediate theorem |

## Status
landed 20261018T071210-L-1674057 2026-10-18 (merge of deliver/P4/Sheaf.Paper.SliceSiteLocalization)
