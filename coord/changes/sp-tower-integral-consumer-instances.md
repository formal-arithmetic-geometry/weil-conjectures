# IntegralDirectImageTower local module-sheaf instance inference (withdrawn)

## Reason

Withdrawn by the reviewer, 2026-10-26 (second time; first on 2026-10-25 for head ab05c97498f).
The worker added to Sheaf.Paper.IntegralDirectImageTower (held by B8) the local commands
`attribute [-instance] spCoefficientModulesAbelian spReconstructionModulesAbelian` and
`attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
HasDerivedCategory.standard` after 60 s timeouts. The adaptation is not forced: the original
module compiles unchanged, without diagnostics, against the delivered modules (29.1 s on
2026-10-26; 24.1 s and 34.1 s on 2026-10-25; published baseline 34.0 s). The timeouts were
caused by machine load. IntegralDirectImageTower is delivered unchanged.

## Old

No change.

## New

No change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralDirectImageTower | B8 | None; module unchanged. |

## Status

withdrawn
