# Exceptional transport support law component split

## Reason

The assigned support theorem concludes equality of two functors. Its proof is decomposed into the strictly simpler object and morphism component equalities required by `CategoryTheory.Functor.ext`.

## Old

The support theorem had proof `by sorry` and the DAG listed one bundled support calculation.

## New

The support theorem applies `CategoryTheory.Functor.ext` using the two new component theorems. The original target statement and all existing definitions are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport | G8 | Uses the two new component modules. |

## Status

landed 20261028T034802-L-3544755 2026-10-28 (merge of deliver/G8/Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport)
