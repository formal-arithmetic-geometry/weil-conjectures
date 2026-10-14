# Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport proof imports

## Reason

The proof uses Mathlib's derived-category exact-functor construction, which is not available
from the module's original imports.

## Old

The module imported only `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`.

## New

The module additionally has the proof-only import
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport | K3 | proof-only import; no public declaration dependency |

## Status

landed 20261014T004106-L-2835751 2026-10-14 (merge of deliver/K3/Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawTransport)
