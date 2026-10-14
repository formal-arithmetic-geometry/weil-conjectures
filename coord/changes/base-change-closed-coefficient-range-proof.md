# AlgebraicGeometry.Etale.baseChange_closed_coefficient_mem_range

## Reason
The completed proof uses local transparency controls for the derived functor definitions while combining the existing base-change identities with the two new closed-coefficient comparisons. The local attributes are required for the proof to elaborate within the file compile limit.

## Old
The item theorem had the original statement and a proof hole. It had no local irreducibility attributes for `CategoryTheory.Functor.mapDerivedCategoryPlus` and `CategoryTheory.Functor.rightDerivedFunctorPlus`.

## New
The theorem has the identical statement and a complete proof. Its file declares the two local irreducibility attributes, used only while elaborating private proof terms; no public definition, theorem signature or visibility changes.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange` | X2 | Local proof elaboration only; theorem statement is unchanged. |

## Status
landed 20261014T170740-L-2556696 2026-10-14 (merge of deliver/X2/Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange)
