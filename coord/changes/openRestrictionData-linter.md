# `H.openRestrictionData` linter scope

## Reason

The theorem's existential witness `e` is intentionally unused in the displayed equations,
which triggers the unused-variable linter during delivery. A module-local option suppresses
that diagnostic without changing the elaborated declaration type.

## Old

No `linter.unusedVariables` option in the module.

## New

`set_option linter.unusedVariables false` in the module section.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenExtTransport | U1 | no elaborated type or proof dependency change |

## Status

landed 20261013T011938-L-2767011 2026-10-13 (merge of deliver/X3/Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenRestrictionData)
