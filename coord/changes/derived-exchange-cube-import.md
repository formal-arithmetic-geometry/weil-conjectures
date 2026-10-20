# Sheaf.SecSmoothPurity.DerivedExchangeCube imports

## Reason

The proof no longer uses the derived inverse-image composition statement module. The proof now
uses the existing derived horizontal pasting theorem, so the unused import is removed.

## Old

`import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`

## New

No import of `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.DerivedExchangeCube | W2 | proof-only import removed; the declaration signature is unchanged |

`tools/downstream.py Sheaf.SecSmoothPurity.DerivedExchangeCube --uses derivedExchangeCube` reports zero downstream modules on this checkout. There are no consumers to adapt. The original theorem signature is byte-for-byte unchanged.

## Status

landed 20261020T131216-L-1260461 2026-10-20 (merge of deliver/W2/Sheaf.SecSmoothPurity.DerivedExchangeCube)
