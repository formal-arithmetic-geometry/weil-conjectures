# ClosedTorsionRigiditySerreTransfer proof imports

## Reason

The item is listed in coord/rework.tsv for a transitive import of
Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero. The unused ScalarMatrixInverseImage
and InternalModuleOperationsTransport proof imports introduce that chain.
Removing unused proof imports repairs the import graph without changing definitions,
statements, visibility, or public imports.

## Old

```lean
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Limits
```

## New

```lean
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClosedTorsionRigiditySerreTransfer | K5 (assigned rework) | Removes unused proof imports; same three public declarations and theorem hole. |

The downstream tool reports no other importing module and no external textual
use of closed_torsion_rigidity_serre_transfer. All public imports are identical.
The mathematical parent in the DAG remains required and is not withdrawn.
No target definition changes meaning, and no consumer adaptation is required.

## Status

landed 20261024T190234-L-4002161 2026-10-24 (merge of deliver/K5/Sheaf.Paper.ClosedTorsionRigiditySerreTransfer)
