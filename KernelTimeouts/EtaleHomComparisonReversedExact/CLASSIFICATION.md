# EtaleHomComparisonReversedExact: exact Kernel site

**Declaration:** `etaleHomComparison_reversedExact_commShift_component`,
origin `8ca2e912b93`. The current master port renames the local monoidal
instance to `DerivedCategory.instMonoidalCategory`.

## Measurements

The declared-type probe `probes/TypeOnly.lean` takes 2.90 s. The historical
Before takes 109.87 s (12,487,664 KB); Kernel skipped takes 3.40 s. The
application-only probe `probes/ApplicationOnly.lean`, which binds
`derivedTensorHomShiftComparison_component` and then uses `sorry`, takes
29.02 s on / 3.20 s skipped. The compact state probe prints the bound result
and the goal. The full original handoff is 110.07 s; After is 3.50 s.

## Exact component

The first expensive application is
`@derivedTensorHomShiftComparison_component ... K n`. Its result uses
`shiftFunctor (DerivedCategory (Sheaf ...))`; the declaration uses
`shiftFunctor (DerivedCategoryModule B X)`. The printed state shows the same
`scalarExtension`, `CommShift`, and `v.app`, but different derived-category
wrappers and category instances under the shifted morphism. Replacing the
transpose premise by a typed `sorry` does not remove the 29 s application
cost, so `hv` is not the hotspot.

Diagnostics on the application-only probe report 421,348 Kernel unfolds of
`Add.add`, 303,281 `Functor.obj`, and 213,332 `DFunLike.coe`. This is the
conversion under the shifted `v.app`, not an elaborator timeout.

## Classification

Primary mechanism: **E**. Contributing mechanisms: **A** and **C**. Evidence:
**confirmed** for the application boundary and **strongly supported** for the
mechanism. The fixed proof stores the generic result in `h` and closes with
`transport_exact`, so the wrapper conversion is replaced by small endpoint
transport.
