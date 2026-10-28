# WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_unit_normalization

## Reason

The arbitrary unit field in CompletedTensorCommonLiftTensorUnit is not normalized.
The existing obstruction to the universal right-unit assertion used cancellation
only. The new theorem additionally constructs the unique comparison that actually
satisfies the right-unit equation at the common coefficient unit. It is a useful
normalization step toward selecting valid data, with no new holes.

## Old

No declaration with this name or existence-and-uniqueness statement.
The existing declarations in the assigned module keep their exact signatures.

## New

The new module `Sheaf.Paper.AdicCompletedTensorCommonLiftUnitNormalization` proves
that, for each fixed tensorator datum, there exists exactly one isomorphism from
the native unit to ordinary(U) satisfying the right-unit equation at U, where U
is the common coefficient unit. The exact Lean signature is recorded in node
`lem-sf-adic-completed-tensor-common-lift-unit-normalization`.

No existing definition, statement, instance, attribute, or public import changes.
The item's obstruction proof imports and uses the new theorem. Its existing
right-unit hole remains explicitly disputed and is not counted as closed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit | F3 | Existing obstruction proof uses uniqueness of the new normalized comparison; all signatures unchanged. |

All existing indirect users see the same statements and public import closure.
There is no forced adaptation of another group's module.

## Status

landed 20261028T055646-L-790474 2026-10-28 (merge of deliver/F3/Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit)
