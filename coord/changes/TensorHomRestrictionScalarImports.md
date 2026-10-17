# AlgebraicGeometry.Scheme.Modules.tensorHom_restriction_of_local_scalar

## Reason

Prune the unused public import of `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule`
and repair the duplicate-helper refusal at returned head `cc2bc1994c`.
The internal-Hom section module structure already comes from the tensor product
imports. Import the actual upstream comparison module with `import all` to use
its existing private theorem `AlgebraicGeometry.Scheme.Modules.tensor_hom_ext`.
The intervening Sheaf module is only a re-export and does not expose that private
theorem through `import all`. Remove the duplicated local helper and its now-unused
direct bilinear-universal import. No source-library module is modified.

## Old

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison
```

## New

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison
```

The existing public declaration's complete old and new signatures are identical.
No definition or intermediate statement is changed, and no helper declaration is
added. Compared with the returned sandbox, the private duplicated helper is deleted
and its application is replaced by `apply tensor_hom_ext`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.TensorHomRestrictionScalar --uses
 tensorHom_restriction_of_local_scalar` finds two textual uses, including the item's
own declaration. The sole direct importer uses this module through an ordinary
proof-only import. Its source and all signatures are unchanged. The current syntactic
downstream closure contains 898 modules; the public import path ends at the direct
consumer's proof-only import, so the import removal is not re-exported beyond it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorHomRestrictionScalar | M3 | Remove the unused public import and duplicate helper; prove the existing theorem with the upstream extensionality theorem. Public signature unchanged. |
| Sheaf.AlgebraicGeometry.CoherentOpenMapTensorExtension | unclaimed | Uses the unchanged theorem. Compiled unchanged against the repaired module in 18.5 seconds, with no warnings. |

No adapted module is delivered. Target signatures and definitions used by targets
are unchanged, so this cleanup does not alter any mathematical target statement.

## Status

landed 20261017T003424-L-3316258 2026-10-17 (merge of deliver/M3/Sheaf.AlgebraicGeometry.TensorHomRestrictionScalar)
