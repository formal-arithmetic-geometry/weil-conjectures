# Sheaf.AlgebraicGeometry.FinitePresentationAffineSectionsRealization

## Reason

The generated stage-3 probe contains a 101-character line and otherwise emits
no warnings. A file-local option suppresses this style warning so delivery can
run without changing the proof or the generated tool.

## Old

No `set_option linter.style.longLine` command.

## New

`set_option linter.style.longLine false`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FinitePresentationAffineSectionsRealization | W4 | suppresses probe-only style warning |

## Status

landed 20261013T143551-L-562855 2026-10-13 (merge of deliver/W4/Sheaf.AlgebraicGeometry.FinitePresentationAffineSectionsRealization)
