# AlgebraicGeometry.Scheme.exists_small_finiteSubsum_diagram (public imports)

## Reason

The finite-subsum proof needs abelian finite biproducts and colimits, but no
enough-injectives theorem. Its public signature uses `moduleRings`, already
provided by `Sheaf.Paper.DerivedHomMayerVietoris`. Prune the unnecessary public
import edge to the enough-injectives module. The existing theorem signature and
visibility stay identical, and no definition changes.

## Old

```lean
public import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Category.Preorder
```

## New

```lean
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Category.Preorder

import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
```

## Users

`tools/downstream.py` reports one direct importer and 406 transitive importers.
The direct importer imports this module only for its proof, so the removed public
import was never re-exported through that importer. It already publicly imports
`Sheaf.Topology.RingedSpaceModuleCohomology`, which itself publicly imports the
enough-injectives module. Thus every formerly visible dependency remains available
there through that independent path. No downstream adaptation is forced.

`tools/downstream.py --uses moduleSheaves_abelian_enoughInjectives` finds the two
additional textual users listed below; both retain their existing independent
imports. No target statement or definition used in a target changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QcqsCohomologyFiniteSubsumRepresentatives | unclaimed | No change: independently imports RingedSpaceModuleCohomology publicly. |
| Sheaf.AlgebraicGeometry.FormalFunctionsCompleteBase | unclaimed | No change: directly imports RingedSpaceModuleCohomology publicly. |
| Sheaf.Paper.GradedCohomologyModuleFinite | unclaimed | No change: uses the theorem through its existing cohomology imports; the private import of this item in the sole direct importer is not re-exported. |

## Status

landed 20261013T022422-L-3216768 2026-10-13 (merge of deliver/P3/Sheaf.AlgebraicGeometry.QcqsCohomologySmallSubsumDiagram)
