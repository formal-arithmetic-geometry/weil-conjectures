# AlgebraicGeometry.Etale.etale_pullback_twist_tor_window

## Reason

The proof and its two private helpers use the canonical sheaf tensor structure.
The statement already supplies this exact structure explicitly at every tensor
expression, and `pullbackTwistComplexMonoidal` names the induced complex structure.
Activating the existing sheaf instance locally makes the proof use those canonical
structures without carrying large instance-valued local let expressions through the
proof. The preflight treats every added top-level attribute command conservatively
as an interface change and requests this record. The instance attribute is local:
importing modules do not inherit an instance registration.

## Old

No local instance activation after `pullbackTwistDerived`. The theorem proof was
`by sorry`. All three public definitions and the complete theorem signature are
preserved verbatim.

## New

```lean
attribute [local instance] Sheaf.monoidalCategory
```

This command follows the three unchanged public definitions and precedes only new
private helpers and the proved theorem. There is no new definition of a tensor
structure, and no public declaration signature or public import is changed.
The helper definitions have complete bodies and the helper theorem is proved.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtalePullbackTwistTorWindow
--uses etale_pullback_twist_tor_window` reports zero downstream modules and only the
item itself as a textual user. Ripgrep agrees. The DAG's unfinished parents remain
attached and unchanged; the item's statement and its mathematical meaning stay the same.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtalePullbackTwistTorWindow | Q8 | Existing canonical tensor instance used locally in private helpers and theorem proof; signatures and definitions unchanged. |

No consumer adaptation is required. No target statement or definition used by a target
changes.

## Status

landed 20261023T151942-L-427271 2026-10-23 (merge of deliver/Q8/Sheaf.AlgebraicGeometry.EtalePullbackTwistTorWindow)
