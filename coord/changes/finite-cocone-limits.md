# finiteCocone_limits

## Reason
The static delivery checker treats the module-level linter option as a visible
command change and requires this record. The existing signature has an unused
existential binder L; preserving it byte for byte requires suppressing that warning
for a warning-free delivery. No declaration interface or definition changes.

## Old
```lean
public import Sheaf.CategoryTheory.ExactCoupleConvergence
```
There was no module-level linter setting.

## New
```lean
public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.FiniteCoconeStationary
```
After the exposed public section:
```lean
set_option linter.unusedVariables false
```
The new import is proof-only. All existing signatures and definitions are unchanged.

## Users
| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FiniteCoconeExactCouple | not inspected; no adaptation | None: existing signature and public imports unchanged |

## Status
landed 20261013T022429-L-3219042 2026-10-13 (merge of deliver/S1/Sheaf.CategoryTheory.FiniteCoconeLimits)
