# cechInverseImage_degree_zero: import pruning

## Reason

The proof concerns only abelian sheaves and degree zero. It needs `invImage`, `constIso`,
and the shared cohomology instances from `FlatCohomologyComparison`, plus the explicit
cochain map. It does not need `CechComparisonSystem` or its module-coefficient transport.
Replace the overly broad public import by the module defining the objects in the statement.
The declaration's signature and visibility are identical. The added `open
CategoryTheory.Abelian` resolves the Ext namespace in private proofs and exports no data,
notation, instance or declaration.

## Old

```lean
public import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem
public import Sheaf.AlgebraicGeometry.Cohomology.CechInverseImageCochainMap
```

## New

```lean
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Sheaf.AlgebraicGeometry.Cohomology.CechInverseImageCochainMap
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Cohomology.CechComparisonInverseImageUnit | unclaimed | Sole direct importer; already publicly imports CechComparisonSystem itself, so it keeps every declaration previously available through this module. No adaptation. |

All transitive importers pass through this direct importer and therefore retain the
removed public dependency through its own public import. The source import-pruning
checker passes. No definition used by a target changes; no target statement changes.
No module other than the assigned item is adapted.

## Status

landed 20261013T003202-L-2430600 2026-10-13 (merge of deliver/V4/Sheaf.AlgebraicGeometry.Cohomology.CechInverseImageDegreeZero)
