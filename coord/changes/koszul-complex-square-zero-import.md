# ExteriorAlgebra.koszulComplex

## Reason

Mathlib proves contraction square-zero directly, so the public import of the
separately holed square-zero theorem is unnecessary. Removing it prunes that module
from the import closure through KoszulComplex. All existing declarations and definitions
keep their signatures and visibility.

## Old

```lean
public import Sheaf.Paper.KoszulDifferentialSquareZero
```

## New

The import is removed. `CliffordAlgebra.contractLeft_contractLeft`, already available
through `Sheaf.Paper.KoszulDifferential`, proves the composition equation directly.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Downstream importers of Sheaf.Paper.KoszulComplex | unchanged | No library module uses koszul_differential_square_zero; its only import was KoszulComplex. All other declarations exported by the removed module already come from the retained public import of KoszulDifferential. |

A repository-wide search for `KoszulDifferentialSquareZero` and
`koszul_differential_square_zero` finds only its own module and the old import.
There are no forced adaptations.

## Status

landed 20261012T144122-L-2099717 2026-10-12 (merge of deliver/J3/Sheaf.Paper.KoszulComplex)
