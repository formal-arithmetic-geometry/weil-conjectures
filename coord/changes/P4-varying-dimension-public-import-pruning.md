# VaryingDimensionDualizingInverse redundant public import

## Reason

The item does not use any declaration from the separate general coefficient
adjunction construction. Its statements use the normalized clopen comparison
records already supplied by its public `FiniteClopenExceptionalRestriction`
import. Remove the unused public import while adding only private imports for
the two new proof lemmas. All existing declaration signatures and data are retained.

## Old

```lean
public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.Paper.FiniteClopenExceptionalRestriction
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
```

## New

```lean
public import Sheaf.Paper.FiniteClopenDerivedDecomposition
public import Sheaf.Paper.FiniteClopenExceptionalRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed in checked records | Uses the geometric partition and finite inverse theorem; both retain their exact signatures. Compiled unchanged against the delivery. |

This removes a direct re-export only. The general coefficient adjunction module
remains needed transitively in other proofs, so it is not claimed as a globally
pruned module. Target definitions and statements do not change.

## Status

landed 20261027T180726-L-3895569 2026-10-27 (merge of deliver/P4/Sheaf.Paper.VaryingDimensionDualizingInverse)
