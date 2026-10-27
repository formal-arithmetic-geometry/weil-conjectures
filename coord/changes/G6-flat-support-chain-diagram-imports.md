# AlgebraicGeometry.Etale.flatSupportChainDiagram

## Reason

Prove the unchanged theorem using the ordinary adjunction and strong monoidal
cochain comparison API. Replace broad unused imports by the ambient category
instances its declarations need. Add only private proof imports for the inverse
comparison summand formula and exact coproducts/functor categories.
No definition body, existing signature or visibility changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.OpenClosed.Supports
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
```

## New

```lean
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.FromJoel.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Abelian.FunctorCategory
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FlatSupportChainDiagram`
reports zero downstream Lean modules. No consumer needs adaptation.
The item's DAG parents and the unit route remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatSupportChainDiagram | G6 | Proof completed; imports narrowed; existing declarations unchanged |

## Status

landed 20261023T231149-L-3554663 2026-10-23 (merge of deliver/G6/Sheaf.AlgebraicGeometry.FlatSupportChainDiagram)
