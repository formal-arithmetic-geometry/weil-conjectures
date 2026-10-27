# WeilConjectures.TwistFrobeniusScalar.reductionH

## Reason

The item now exposes a named reduction/localization component theorem whose signature mentions the existing `reductionH` construction. The construction itself is unchanged; this record documents the interface dependency detected by the stage-3 checker.

## Old

(n : ℕ) (m : ℤ) : (ModuleCat.extendScalars (reduction l E n)).obj (integralH D l hl E m 0) ⟶ finiteH D l E n m 0

## New

(n : ℕ) (m : ℤ) : (ModuleCat.extendScalars (reduction l E n)).obj (integralH D l hl E m 0) ⟶ finiteH D l E n m 0

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TwistFrobeniusScalar | F4 | The new reduction/localization component theorem uses `reductionH` in its conclusion. |

## Status

landed 20261025T213246-L-310491 2026-10-25 (merge of deliver/F4/Sheaf.Paper.TwistFrobeniusScalar)
