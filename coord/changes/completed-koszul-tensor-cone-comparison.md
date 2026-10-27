# Sheaf.Paper.CompletedKoszulTensorConeComparison

## Reason

The proof needs a local `MonoidalPreadditive` instance for the completed module tensor category, with its coefficient sheaf made explicit so Lean can infer the additive tensor APIs. The generic tower helper module also supplies proof-only declarations used by the assigned theorem.

## Old

No local instance was present in the assigned module; the generic tower helpers were in the item module.

## New

The assigned module declares the local instance `coneComparisonPreadditive`. Generic cone and strict-tower helpers are in `Sheaf.Paper.CompletedKoszulTensorConeComparisonAux`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedKoszulTensorConeComparison | P5 | supplies the local proof instance |
| Sheaf.Paper.CompletedKoszulTensorConeComparisonAux | P5 | new proof-only helper module |

## Status

landed 20261027T034721-L-3678701 2026-10-27 (merge of deliver/P5/Sheaf.Paper.CompletedKoszulTensorConeComparison)
