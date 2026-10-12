# linter-style-haveILetI setting

## Reason
The proof uses local typeclass instances inside a proposition. Mathlib's style linter reports these as warnings, and delivery rejects warning output. Suppress this local style warning so the proof compiles cleanly.

## Old
No `set_option linter.style.haveILetI` setting.

## New
`set_option linter.style.haveILetI false` in `Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg | U1 | proof-only linter setting; theorem signatures unchanged |

## Status
landed 20261012T202254-L-709524 2026-10-12 (merge of deliver/U1/Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg)
