# Sheaf.Algebra.Homology.FilteredTensorGradedComparison public imports

## Reason

The proved comparison no longer uses the specialized second-factor derived tensor
functor. Its derived comparisons instead use the source library's generic K-flat
localization counit. Prune the unused public import. This changes the exported import
closure, so it needs this record even though no declaration signature or definition
changes. No target statement or the meaning of a definition changes.

## Old

```lean
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
```

## New

The import is removed. The replacement proof imports are private:

```lean
import Sheaf.Algebra.Homology.FlatConvolutionGradedIso
import Sheaf.Algebra.Homology.FlatKFlatExtension
import Sheaf.CategoryTheory.DerivedCountableSumsExact
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
```

All existing declarations, their signatures and visibility are retained. This does not
withdraw `DerivedTensorSecondFactorFunctor`, which remains explicitly imported by
`FilteredTensorLocalization`.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.FilteredTensorGradedComparison` lists the
following two current downstream modules. Neither has a current claim in the shared
claim directory. Both original sources compile unchanged against the sandbox outputs
through `lcompile.py`. No consumer is adapted in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FilteredTensorLocalization | unclaimed | Explicitly imports DerivedTensorSecondFactorFunctor itself; unchanged, compiles in 33.0 s. |
| Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement | unclaimed | Does not use the specialized second-factor interface; unchanged, compiles in 7.9 s. |

The item's own module is held by P1. No source-library module changes, and no forced
adaptation of a module held by another group occurs.

## Status

landed 20261020T235613-L-1195016 2026-10-20 (merge of deliver/P1/Sheaf.Algebra.Homology.FilteredTensorGradedComparison)
