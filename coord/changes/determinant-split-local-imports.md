# Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal imports

## Reason

The duplicate local construction theorem was retired because the canonical
`determinant_split_comparison_exists` already provides the complete result. The
remaining restriction theorem uses only the imports in the new header; the old
`Invertible` and `ShortComplex.Basic` imports are unnecessary.

## Old

```lean
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Homology.ShortComplex.Basic
```

## New

```lean
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal | G1 | Header and proof use the new imports. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | Direct importer; compiles unchanged against the new header, with no adaptation required. |

## Status

landed 20261014T050217-L-1646662 2026-10-14 (merge of deliver/G1/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal)
