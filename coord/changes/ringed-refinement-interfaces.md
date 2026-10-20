# SheafOfModules.RingedRefinement interfaces

## Reason

The component theorem modules need the existing RingedRefinement interfaces.
Keeping those interfaces in the item module would create an import cycle when the
item imports the component results. Move those interfaces unchanged into
RingedRefinementData, which the original item publicly imports.

## Old

All declarations in `SheafOfModules.RingedRefinement`, from `Rings` through
`FiniteNormalization`, appeared in the item module.

## New

The same declarations, signatures, visibility and bodies appear in
`lean/Sheaf/Paper/RingedRefinementData.lean`. The original item publicly imports it
and retains the target declaration with its exact original signature. Component
results import the data module and the item assembles them.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedRefinementCoefficientSquare | B6 | Publicly reexports unchanged interfaces and assembles the package theorem. |

No downstream module uses this package interface. No held module is adapted.

## Status

landed 20261020T051031-L-1537613 2026-10-20 (merge of deliver/B6/Sheaf.Paper.RingedRefinementCoefficientSquare)
