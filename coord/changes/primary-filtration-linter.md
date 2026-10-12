# Primary filtration transport linter setting

## Reason

The item keeps its nested action-on-germs hypothesis verbatim. The names hτ and hx occur as
binders in that public hypothesis but are used only to constrain the following equality.
The linter otherwise warns on these bound names. This option changes diagnostics only;
it does not change any declaration type, visibility, definition or target meaning.

## Old

No module-level `linter.unusedVariables` setting.

## New

`set_option linter.unusedVariables false` in
`Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafTransport`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | No signature or proof adaptation; the linter option has no effect on imported declarations. |

## Status

landed 20261012T223415-L-1640273 2026-10-12 (merge of deliver/R3/Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafTransport)
