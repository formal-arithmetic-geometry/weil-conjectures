# Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds imports

## Reason

Remove the unused public import of slice derived restriction while proving the
existing theorem. The statement uses the actual-ring derived inverse image
provided by `NoetherianStratumDetection`; it never uses slice restriction.
The final file compiles without this import, with the existing theorem's
signature unchanged. The public homology import is retained because the statement
uses `DerivedCategory.homologyFunctor`.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Data.Finset.Max
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds | S9 | Complete proof; unchanged theorem signature; remove unused public slice-restriction import. |

`tools/downstream.py` reports 0 downstream modules and only the item itself
using `AlgebraicGeometry.Scheme.exists_global_bounds_of_stratified_local_bounds`.
There are no current Lean importers of this module, hence no consumer adaptation.
The DAG parents remain attached to this theorem with exactly the same statement.
No definition used by any target changes. No source-library file is modified.

## Status

landed 20261021T120521-L-3905356 2026-10-21 (merge of deliver/S9/Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds)
