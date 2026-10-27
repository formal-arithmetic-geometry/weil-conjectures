# exceptional-integral-scalar-mates-linter

## Reason

The data conclusion contains an existential binder whose name is not referenced
by its final `True` body.  The Lean linter consequently emits a warning on this
otherwise unchanged target statement.  The module-level option disables only
that linter so the delivered module compiles without warnings; theorem types and
all declarations are unchanged.

## Old

The module did not set `linter.unusedVariables`.

## New

`set_option linter.unusedVariables false` is set with the existing module options.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalIntegralScalarMates | M3 | suppresses a declaration-linter warning; no type or name changes |
| Sheaf.Paper.ExceptionalRingTransportFamily | unclaimed | compiles against the unchanged theorem interfaces |
| Sheaf.Paper.ExceptionalIntegralSupportAdjoint | unclaimed | compiles against the unchanged theorem interfaces |
| Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction | unclaimed | compiles against the unchanged theorem interfaces |

## Status

landed 20261027T234101-L-4186359 2026-10-27 (merge of deliver/M3/Sheaf.Paper.ExceptionalIntegralScalarMates)
