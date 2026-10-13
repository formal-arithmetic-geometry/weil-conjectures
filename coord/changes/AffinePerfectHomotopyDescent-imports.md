# Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent imports

## Reason

The public import Mathlib.Algebra.Category.ModuleCat.Abelian is unused by the
statement and proof. ModuleCat.ChangeOfRings, already publicly provided by
ScalarExtensionHom, provides the module category and its preadditive structure.
The item compiles cleanly after removing this import. All existing theorem
signatures and definitions remain byte-for-byte unchanged.

## Old

```lean
public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Colimits
```

## New

```lean
public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
```

## Users

Ran tools/downstream.py Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent
--uses affine_perfect_homotopy_descent on the read-only repository. The only
user of the theorem outside its defining module is AffinePerfectHomColimit,
which is also the sole direct importer. Its line 9 already publicly imports
Mathlib.Algebra.Category.ModuleCat.Abelian. Consequently every transitive
importer still obtains that module through this same caller, and none of the
408 downstream modules loses access to it. No target statement changes its
meaning; this is exclusively redundant-import removal. No modules are adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent | V1 | Removes an unused public import; compiles cleanly; theorem unchanged. |
| Sheaf.AlgebraicGeometry.AffinePerfectHomColimit | unclaimed | No effect: explicitly publicly imports ModuleCat.Abelian already. |

## Status

landed 20261013T100154-L-2494996 2026-10-13 (merge of deliver/V1/Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent)
