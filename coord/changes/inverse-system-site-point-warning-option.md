# CategoryTheory.inverseSystemSitePoint: warning-option cleanup

## Reason

The return for delivery head `ea940d8a0a` reports an unattributed hole at line 33,
the top-level `set_option warn.sorry false` command. The landing census matches
the option name as a hole marker. Remove this unnecessary warning suppression.
The retained complete proof closes the theorem's original hole. No declaration
signature, public import, definition, or mathematical meaning changes.

The dry-run interface checker requires this record because a top-level command
changes. This is a diagnostic-option change, not a statement or definition repair.
It does not reopen target statement review.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

## Users

`python3 tools/downstream.py Sheaf.TraceFormula.InverseSystemSitePoint
--uses inverseSystemSitePoint` reports the following three downstream modules;
none currently mentions the theorem name. Their statements and proofs are
unaffected: imported module options do not alter their mathematical interfaces.
No consumer adaptation is required or included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.InverseSystemSitePoint | M1 | Warning suppression removed; proof complete. |
| Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints | G4 | No change required. |
| Sheaf.CategoryTheory.Sites.FinitarySliceEnoughPoints | H3 | No change required. |
| Sheaf.Paper.FinitarySiteEnoughPoints | J4 | No change required. |

Validation: the repaired module compiles cleanly through `lcompile.py` in 1.6 s.
A separate compile with `#print axioms CategoryTheory.inverseSystemSitePoint`
reports only `propext`, `Classical.choice`, and `Quot.sound`. No holes remain.

## Status

landed 20261020T162315-L-3588610 2026-10-20 (merge of deliver/M1/Sheaf.TraceFormula.InverseSystemSitePoint)
