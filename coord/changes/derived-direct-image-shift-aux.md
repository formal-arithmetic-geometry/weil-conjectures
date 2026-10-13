## Reason

The target proof needs a separately named component identity whose proof is left for a later worker.

## Old

There was no auxiliary module or declaration; the target module contained only its original public imports and target theorem.

## New

A proof-only import of `Sheaf.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparisonAux` is added to the target. The new module declares `derivedModuleDirectImageKInjectiveIso_shift_aux` and leaves its proof as a documented sorry.

## Users

The only user is `Sheaf.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparison`, which invokes the auxiliary theorem in the target proof. No existing external declaration changes.

## Status

landed 20261013T190202-L-3224305 2026-10-13 (merge of deliver/V4/Sheaf.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparison)
