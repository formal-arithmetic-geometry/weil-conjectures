# Sheaf.AlgebraicGeometry.ShiftedEtaleLinesLocality proof context

## Reason

The proofs use the existing ordinary-etale source interfaces, so remove unused proof-plan
imports, including the public PointedEtaleStalk import. Both theorem signatures use the
existing pointSmallEtale.sheafFiber interface exposed by the retained source imports.
Open Limits and MonoidalCategory locally for tensor notation, unitors, braiding and flatness.
Use the same local braiding-instance priority as upstream SmoothDuality.Local, avoiding
unnecessary coefficient-instance unfolding. The theorem signatures, universes, hypotheses,
definitions and target statements are unchanged.
No source-library module is changed.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.SixFunctors.EtaleStalkConstantComplexExactness
import Sheaf.SixFunctors.EtaleDerivedPullbackStalk
import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.CategoryTheory.RingedSiteModules
open CategoryTheory AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace
open CategoryTheory AlgebraicGeometry.Scheme Limits MonoidalCategory
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ShiftedEtaleLinesLocality | T3 | Proofs and file imports only; theorem signatures unchanged. |

`tools/downstream.py` reports zero downstream modules for this module.
Its two `--uses` checks report only their respective declarations in this module.
There are no consumers to adapt. The module stays available for its DAG parents.
The removed public import changes the transitive export surface, but no current user
relies on it; both theorem statements still elaborate through the retained imports.
No target statement or definition used by one is changed.

## Status

landed 20261023T103309-L-3093656 2026-10-23 (merge of deliver/T3/Sheaf.AlgebraicGeometry.ShiftedEtaleLinesLocality)
