# primitiveQuotientScalarModelExistence

## Reason

The proof imports two proof-only modules and adds two public helper theorems: a
realization construction and a strictly smaller normalization statement. This
changes the module interface and is recorded for CODEX review.

## Old

The module publicly imported only `Sheaf.Paper.IntegralComparisonRealizationModels`
and exposed `primitiveQuotientScalarModelExistence` with an admitted proof.

## New

The module additionally imports `Sheaf.Paper.CoefficientExtensionReductionModel`
and `Sheaf.Paper.TransportedReductionScalarNormalized`, proves
`primitiveQuotientScalarModelRealization`, leaves the strictly smaller
`primitiveQuotientScalarModelNormalization` split, and proves
`primitiveQuotientScalarModelExistence` by packaging those fields.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PrimitiveQuotientRealizationComparisons | S6 | imports the item; unchanged theorem application |
| Sheaf.Paper.EffectiveQuotientModelDescent | Q23 | transitive importer; no signature change |

## Status

landed 20261026T114207-L-2272853 2026-10-26 (merge of deliver/N2/Sheaf.Paper.PrimitiveQuotientScalarModelExistence)
