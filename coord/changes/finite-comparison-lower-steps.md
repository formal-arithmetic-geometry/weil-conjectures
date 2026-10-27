## Reason

The finite comparison proof needs a proper-factor invertibility step and the shift route needs the restriction-square shift step. Both are isolated as lower statements.

## Old

The parent module had the combined finite comparison and scalar mate holes without these named lower declarations.

## New

Added `FiniteProperComparisonIso` and `IntegralCompactSupportRestrictionShift`, and imported them proof-only in the parent module.

## Users

Only `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` uses these declarations.

## Status

Compiles locally and is included in this stage-3 delivery.
