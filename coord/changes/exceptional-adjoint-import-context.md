# ExceptionalAdjointAdmissibility proof imports

## Reason

The component proof imports the staged arrow-normalization and constant-support projection
modules so it can use their named declarations.

## Old

The item module did not import these proof modules.

## New

The item module imports `Sheaf.Paper.SupportScalarProjectionNormalization` and
`Sheaf.Paper.ExceptionalSupportProjectionIso`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ExceptionalAdjointAdmissibility | U1 | proof imports |

## Status

landed 20261021T001144-L-1378231 2026-10-21 (merge of deliver/U1/Sheaf.Paper.ExceptionalAdjointAdmissibility)
