# helperSourceCoordinatesAbelian

## Reason

Restore `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers` from the
archive named in `coord/rework.tsv`, retaining all five existing proved helpers,
both public theorem signatures, and all three public imports. The sync introduced
a duplicate tensor-model import, a universe-sensitive sheaf-module abelian
instance, and a globally irreducible `derivedPullback`. The helpers themselves
are generic categorical proofs and need none of the eight removed private imports.

## Old

```lean
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
```

```lean
@[reducible]
local instance (priority := 2000) helperSourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := SheafOfModules.instAbelian Y.ringCatSheaf
```

```lean
attribute [local irreducible] tilde tilde.functor Functor.mapDerivedCategory
  affineTildePushforwardComparison Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback derivedPullback
  schemeDerivedBaseChangeMap
  moduleHomotopyBaseChange
```

## New

The eight private imports above are removed. All public imports and theorem
statements and proofs remain verbatim from the archived item.

```lean
@[reducible]
local instance (priority := 2000) helperSourceCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))
```

```lean
attribute [local irreducible] tilde tilde.functor Functor.mapDerivedCategory
  affineTildePushforwardComparison Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Scheme.Modules.tensorPullback
  schemeDerivedBaseChangeMap
  moduleHomotopyBaseChange
```

## Users

`tools/downstream.py` with `--allow-missing --direct --uses
leftCounit_naturality leftDerived_comparison_on_resolution` reports no active
importers because the item and its consumers are quarantined. Searching both
`lean/` and `quarantine/` finds these two direct consumers. Current claim records
list both as unclaimed. Their public types are unaffected: this delivery changes
only private imports and local elaboration setup.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase | unclaimed | Quarantined; uses the unchanged `leftDerived_comparison_on_resolution`; no forced adaptation. |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre | unclaimed | Quarantined; uses the unchanged `leftCounit_naturality`; no forced adaptation. |

A separate consumer module was compiled together with the repaired helper. It
imports the helper, restates the exact archived types of both public theorems,
and proves them by applying the imported declarations. It also checks the
re-exported `affineTildeFunctor`, `affineTildePushforwardComparison`, and
`SingleComplexBaseChange.counit`. Both public helpers use exactly the allowed
three axioms. The actual quarantined consumers have separate rework assignments;
this delivery neither restores nor modifies them.

No definition in a target statement is changed. No source-library file is changed.

## Status

landed 20261020T151235-L-2653120 2026-10-20 (merge of deliver/T3/Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers)
