# Sheaf.Paper.FinitePerfectQuotientModels restoration

## Reason

Repair the returned quarantined item `Sheaf.Paper.FinitePerfectAdicRealization`.
The assigned theorem's public signature uses the quotient-model predicates, while
the current library contains only a withdrawn stub of
`Sheaf.Paper.FinitePerfectQuotientModels`. Restore the minimum compiling public
interface needed by the assigned module in the same delivery.

## Old

```lean
module
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.ProEtaleConstructibleSheaf

/-! Withdrawn: no declarations remain. -/
```

## New

The module contains the original finite quotient model interface declarations
needed by `FinitePerfectAdicRealization`: the standard site/derived instances,
`finiteModelConstantComplex`, `FinitePerfectModelsOn`,
`HasUniformFinitePerfectModels`, `FinitePerfectModelsNormalized`,
`FinitePerfectModelsCompatible`, and the proved theorem
`finitePerfectModels_normalized_compatible`. The archived successor induction
and aggregate theorem are intentionally not restored here because they are not
used by the assigned module and their archived successor proof is a separate
`sorry` rejected by the stage-3 gate.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.FinitePerfectAdicRealization` | B3 | restores the missing public predicates used in its theorem signature |

## Status

landed 20261020T233051-L-889151 2026-10-20 (merge of deliver/B3/Sheaf.Paper.FinitePerfectAdicRealization)
