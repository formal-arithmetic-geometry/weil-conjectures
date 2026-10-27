# Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA

## Reason
The continuation module had to expose its completed integral construction to four
strict component lemmas. The prefix declarations were moved to a dedicated base
module, which is publicly imported by the continuation. This preserves every
public declaration and lets the component modules depend on the construction
without an import cycle.

## Old
The declarations `podPartialClosed_ext`, `podCompletedTensorUnit`,
`podIntegralClosed_existsUnique`, `podIntegralClosed`,
`podIntegralPairs_pullback`, and `podIntegralHomComparison` were in
`Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA`.

## New
Those declarations are in
`Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase`, and
`Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA` publicly imports
that module.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB` | unclaimed | receives the same declarations through the public base import |

## Status
landed 20261027T233800-L-4114267 2026-10-27 (merge of deliver/B4/Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA)
