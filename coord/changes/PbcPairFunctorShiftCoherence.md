# AlgebraicGeometry.Scheme.pbcPairFunctorShiftCoherence

## Reason

The proof no longer uses the direct `Sheaf.Paper.PbcScalarExtension` and
`Mathlib.CategoryTheory.Triangulated.Functor` imports. It adds only private generic
stage-system helpers adapted from the existing private construction in
`Sheaf.Paper.PbcDescentFunctors`; no public declaration or theorem signature changes.
The stage-3 preflight requires a change record when the module's visible command/import
surface changes.

## Old

The module had proof-only imports of `Sheaf.Paper.PbcScalarExtension` and
`Mathlib.CategoryTheory.Triangulated.Functor`, and the theorem proof was `by sorry`.

## New

Those two unused proof-only imports are removed. The module contains private helpers
`shiftHom`, `shiftIso`, `shiftIso_hom_app`, `descendedCommShift`,
`inclusionComp_commShift`, and `pairFunctorShiftCoherence`; the public predicate and
`pbcPairFunctorShiftCoherence` signature are unchanged. The theorem is proved with no
`sorry`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PbcPairFunctorShiftCoherence | A3 | This is the delivered module; private proof imports and helpers are internal. |

No other module imports or references the removed proof-only imports through this file.
The public imports and all public declarations remain unchanged.

## Status

landed 20261021T134255-L-736769 2026-10-21 (merge of deliver/A3/Sheaf.Paper.PbcPairFunctorShiftCoherence)
