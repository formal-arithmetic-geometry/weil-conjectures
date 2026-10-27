# Sheaf.Paper.LocalizationScalarUnit

## Reason

The statement needs only `FiniteClosedShriek` and the Noetherian declarations.
Remove the two unused public imports and the unused private planned-proof imports.
The theorem's signature is preserved verbatim. The original module has no current
Lean importers; its unfinished DAG parents still need the theorem and are retained.

## Old

```lean
public import Sheaf.Paper.FiniteClosedShriek
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.AlgebraicGeometry.Noetherian
```

## New

```lean
public import Sheaf.Paper.FiniteClosedShriek
public import Mathlib.AlgebraicGeometry.Noetherian
```

The private proof imports and their pruning are listed in `report.md`.
No declaration body other than theorem proofs changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocalizationScalarUnit | S5 | Complete proof; reduced unused exports |

There are no current Lean modules importing this module, as checked by `rg` over
`lean/`. No source-library or target statement changes, and no forced adaptations.

## Status

landed 20261022T145649-L-2037678 2026-10-22 (merge of deliver/S5/Sheaf.Paper.LocalizationScalarUnit)
