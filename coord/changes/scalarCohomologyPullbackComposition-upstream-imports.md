# AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_comp

## Reason

Restore the quarantined composition theorem after upstream sync 5f7b33eac.
The archived module imports both the local scalar operations and, through its
coherence dependency, the upstream copy of the same declarations. Lean rejects
the duplicate `AlgebraicGeometry.Scheme.Modules.externalCupCoefficients`.
The exact-functor comparison also has an adopted upstream copy. Select the
canonical upstream modules consistently. The theorem signature, its proof,
and all definition bodies remain unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ScalarInverseImageCompositionCoherence
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison
import WeilConjectures.AlgebraicGeometry.TensorPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ScalarInverseImageCompositionCoherence
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
```

`TensorPullback` is unused: the normalized comparison is defined in the scalar
operations module, whose public imports already provide the tensor-pullback API.
Comparison of the two scalar operation sources shows identical public definitions
and theorem statements; differences are authorship and local instance names.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | N2 | Restored from quarantine with canonical imports; clean single-file compile. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare | quarantined; separate rework item | Direct archived consumer; theorem name and signature preserved. Its own obsolete scalar-operation import requires its independently assigned sync repair. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | quarantined; separate rework item | Archived transitive consumer through the square theorem; statements preserved. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | quarantined; separate rework item | Archived transitive consumer through Kunneth functoriality; statements preserved. |

There are no current importers under `lean/`: this item and its consumers were
quarantined by the sync. `tools/downstream.py` reports the missing active module;
searching `lean/` and `quarantine/Sheaf/` finds the direct consumer above.
The three archived downstream modules are listed above. No consumer, archive, or DAG attachment is removed.
No target type or mathematical definition changes; the unit route is retained.

## Status

landed 20261020T145532-L-2408424 2026-10-20 (merge of deliver/N2/Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition)
