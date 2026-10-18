# Extended Cech reflector core decomposition

## Reason

The reflector theorem's naturality and unit-isomorphism clauses are formal consequences of the completeness and universal mapping clauses. Isolating those two clauses in a strictly smaller core theorem makes the completed part of the parent proof explicit while leaving the finite localization-filtration argument as one named obligation.

## Old

The module had one admitted theorem `CategoryTheory.ringedExtendedCech_reflector_properties` containing completeness, naturality, universal mapping, and unit-isomorphism clauses together. Its proof also carried private cone and derived-global-sections helpers that were unused by the retained reduction.

## New

Added `Sheaf.Paper.ExtendedCechReflectorCore` with the strictly smaller core theorem `CategoryTheory.ringedExtendedCech_reflector_core`. The parent theorem now combines that core with its proved naturality calculation and the generic universal-unit isomorphism helper. Removed the unused private helpers and their proof-only imports.

## Users

The parent module is the only consumer of the new core declaration. Existing downstream modules retain their interfaces and continue to import the parent module unchanged.

## Status

landed 20261018T091400-L-3254261 2026-10-18 (merge of deliver/E4/Sheaf.Paper.ExtendedCechCompletionModel)
