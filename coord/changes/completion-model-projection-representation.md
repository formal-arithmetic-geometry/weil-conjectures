# Principal quotient completion model projection representation

## Reason

Withdrawn by the reviewer (2026-10-26, delivery head `9c075bb5acfe`). The delivery proposed
turning `structure Model` of `Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel` into an
`abbrev` of a new generic `CompletionModelData`, with eight projection abbreviations, and
turning `noncomputable def quotientRoos` into an `abbrev`. Against that representation four
importers that compile against the published module fail with errors:
`Sheaf.Paper.CompletedIntegralPrincipalUnitCriterion` and
`Sheaf.Paper.CompletedIntegralQuotientModelComparison` (`failed to set [local irreducible]`:
`quotientRoos` is now `[reducible]`, then heartbeat timeouts), and
`Sheaf.Paper.PrincipalCompleteHeartKernels` and `Sheaf.Paper.SupportedKernelImageBaseComplete`
(heartbeat timeouts at `whnf`/`isDefEq`); `CompletedCoefficientFamilyTransportModels` and
`CompletedCoefficientTensorTransportModels` slow down from 17 s / 29 s to 76 s / 98 s.
The item and every other delivered module compile unchanged against the published
`PrincipalQuotientCompletionModel` (reviewer compile: item 49.6 s / 52.9 s, all 26 checked
importers without error). The module stays at its published version.

## Old

`structure Model` and `noncomputable def quotientRoos`, as published.

## New

Unchanged (no change is made).

## Users

None affected: the declarations are unchanged.

## Status

withdrawn
