# Sheaf.Paper.CondensedPointModuleComparison public imports

## Reason

The five completed proofs use the existing internal-module and unbounded-derived APIs.
Their signatures and the comparison definition are unchanged. Remove unused imports,
including statement packages that the declarations never reference. Both retained public
imports provide everything in the public statements and definition. This changes exported
imports only; it changes no target, coefficient map, category, or mathematical definition.

## Old

```lean
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
```

## New

```lean
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Algebra.Category.Grp.AB

meta import Mathlib.Lean.Meta.CongrTheorems
```

## Users

`python3 tools/downstream.py Sheaf.Paper.CondensedPointModuleComparison
--uses condensedPointModule` reports zero downstream modules and zero declaration users.
The DAG parent `lem-zl-condensed-lisse-proetale-locality`, attached to
`Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality`, still needs the unchanged
comparison statements; its unfinished proof does not yet import this module. It requires
no adaptation. The item and its DAG attachment are retained.

| module | group holding it | effect |
|---|---|---|

There are no current Lean importers to adapt. All original declaration signatures,
visibility and the public definition body are preserved; local reducibility settings
apply only inside this file. The independent reader can compare these directly.

## Status

landed 20261024T191445-L-376659 2026-10-24 (merge of deliver/V1/Sheaf.Paper.CondensedPointModuleComparison)
