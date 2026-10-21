# AlgebraicGeometry.Scheme.IsIntegralStratifiedPerfect and IsIntegralStratifiedFinitelyPresented

## Reason

The quarantined source used an obsolete `LocallyClosedStratification` name that is absent from the
current library. The current project definition is `Scheme.Stratification`, which additionally
records constructibility of strata and is the intended interface for constructible pro-etale
models.

## Old

`∃ s : LocallyClosedStratification T, ...`

## New

`∃ s : Stratification T, ...`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | A3 | Updated the two definitions to the current stratification interface. |
| Sheaf.AlgebraicGeometry.ProEtaleConstructibleSheaf | unclaimed | Uses the current constructible stratification definitions; no adaptation required. |

## Status

landed 20261021T011009-L-2026612 2026-10-21 (merge of deliver/A3/Sheaf.Paper.IntegralStratifiedPerfectCharacterization)
