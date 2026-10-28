# Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization public imports

## Reason

The completed supported-source normalization is an ordinary categorical calculation.
It uses no canonical right-derived construction. Remove the redundant public import
of `Sheaf.Paper.CanonicalDiagonalRightDerived`; the theorem statement is unchanged.

## Old

```lean
public import Sheaf.Paper.DiagonalCompletedPushSquare
public import Sheaf.Paper.CanonicalDiagonalRightDerived
```

## New

```lean
public import Sheaf.Paper.DiagonalCompletedPushSquare
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedSupportedCoefficientTransport | unclaimed | Its own public import of CanonicalDiagonalRightDerived already supplies that interface; no adaptation is needed. |

This is the sole direct importer, checked against the current server claims.
No declaration signature, instance, definition, or exported attribute changes.
The delivery tool compiles the unchanged consumer against this packet.

## Status

landed 20261028T020721-L-2541097 2026-10-28 (merge of deliver/S1/Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization)
