# Tor localization denominator interface

## Reason

The proof adds private scoped helper declarations and proof-only imports. The module-level `open MonoidalCategory` and `open scoped TensorProduct` commands are visible to importers according to the stage-3 interface checker. They are retained for the existing public statement and proof elaboration.

## Old

The module had no proof-only imports, no `open MonoidalCategory`, and no `open scoped TensorProduct` commands.

## New

The module imports `Mathlib.RingTheory.Localization.BaseChange` and `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, and opens `MonoidalCategory` and scoped `TensorProduct` notation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.TorVanishingLocalizedAlgebra | unclaimed | proof elaboration sees the additional imports and notation; public declarations are unchanged |

## Status

landed 20261013T121510-L-3529412 2026-10-13 (merge of deliver/J1/Sheaf.RingTheory.TorLocalizationDenominators)
