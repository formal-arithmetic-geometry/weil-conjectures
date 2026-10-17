# DerivedDirectImageBoundedBelowQCoh namespace opening

## Reason

The proof uses the categorical limits API (`IsZero`, `cokernel`, and related declarations)
without qualification. The module therefore opens `CategoryTheory.Limits` for its proof.

## Old

`open CategoryTheory`

## New

`open CategoryTheory CategoryTheory.Limits`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh | B4 | required by the proof |

## Status

landed 20261017T003415-L-3312843 2026-10-17 (merge of deliver/B4/Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh)
