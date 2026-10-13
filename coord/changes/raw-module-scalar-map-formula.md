## Reason
The repository lacked the imported coefficient source module, so the assigned formula could not compile.
## Old
The formula imported Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare, which was absent.
## New
The required scalar source and coefficient factor definitions are included in the assigned module, with the same declarations and bodies.
## Users
Only the assigned formula module uses these declarations in this delivery.
## Status
landed 20261013T234521-L-2167133 2026-10-13 (merge of deliver/S2/Sheaf.AlgebraicGeometry.RawModuleScalarMapFormula)
