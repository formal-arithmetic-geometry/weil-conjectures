# Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation public imports

## Reason

The completed proof uses the existing canonical exact-functor comparison and the original
internal-module boundedConstructible predicate. The pro-etale point alias, discrete
coefficient-sized constructibility interface and alternative total-tensor left-derived
comparison are unused. Removing their public imports removes unnecessary exported
interfaces and dependencies. This is an import-only interface change: every existing
public declaration, its signature, visibility and definition body stay unchanged.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact
public import Sheaf.Paper.CondensedCoefficientComparisons
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.Paper.CondensedCoefficientComparisons
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation | U3 | Its completed proof compiles with the reduced imports. Both public declarations keep their exact signatures and the canonical comparison keeps its exact definition. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation`
reports zero downstream modules. Searches of all live and quarantined Lean files find no
importers or external mentions of its theorem or comparison. Consequently there is no
consumer to adapt. The DAG parents remain valid and are not withdrawn: the theorem still
provides every original conclusion and the new proof follows the same finite-field
triangulation and ambient exact-extension route. No target statement or definition changes.

## Status

landed 20261021T155800-L-3449027 2026-10-21 (merge of deliver/U3/Sheaf.AlgebraicGeometry.ConstructibleExactScalarTriangulation)
