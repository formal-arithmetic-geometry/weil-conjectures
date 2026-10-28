# WeilConjectures.AdicSmoothDualizing.levelSetting

## Reason

The module exceeded the 60-second compilation limit. The finite-setting wrapper
only changes the positive level; hiding its unchanged field projections forced
broad transparency overrides during instance search and repeated elaboration.
Use a transparent abbreviation for exactly the same record value. This also
allows the finite integration definition to infer the identity base morphism's
finite-type instance under normal transparency settings. The explicit single
comparison in `finiteUnitPlus` is replaced by the existing exact-functor
lower-bound theorem. No mathematical object, hypothesis or conclusion changes.

## Old

```lean
def levelSetting (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_pos n }
```

## New

```lean
abbrev levelSetting (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_pos n }
```

## Users

The current `tools/downstream.py --uses levelSetting` finds the item itself and
the two RationalSmoothPurity modules below. The other two are its remaining
direct importers. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothDualizingComplexes | M2 | same value, earlier projection reduction |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | same statement and data |
| Sheaf.Paper.RationalSmoothPurityFiniteTrace | unclaimed | same statement and data |
| Sheaf.Paper.PurityOrientationDatum | unclaimed | no direct use of levelSetting |
| Sheaf.Paper.PoincareDualityConventions | unclaimed | no direct use of levelSetting |

Consumer checks are recorded in report.md. PoincareDualityConventions and
RationalSmoothPurityFiniteTrace passed. Canonical exceeds the time limit also
against the published item baseline, and OrientationDatum is blocked by a missing
published dependency artifact. There are no consumer source edits in this packet.

The wrapper's value is identical, so targets using it retain their meaning.
The change affects elaboration transparency only.

## Status

landed 20261028T055716-L-798391 2026-10-28 (merge of deliver/M2/Sheaf.Paper.AdicSmoothDualizingComplexes)
