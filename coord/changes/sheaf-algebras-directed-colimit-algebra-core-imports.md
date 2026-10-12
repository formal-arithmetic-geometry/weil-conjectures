# sheafAlgebras_directed_colimit_algebra_core imports

## Reason

The complete proof uses Mathlib's sectionwise-colimit and sheafification APIs and a direct
Under-category universal-property argument. It does not use the underlying module of an
algebra sheaf, equivalences of sites, or a separately imported filtered-category API.
Replace the CommAlgebraSheafModule import with the two Mathlib imports that supply the
statement's sheaf and ring types; Under is already available through Sites.LeftExact. Sites.Limits is already publicly imported
by Sites.LeftExact; Filtered.Basic is already publicly available from Ring.FilteredColimits.
The declaration's signature and all definitions used by the targets are unchanged.

## Old

```lean
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
```

## New

```lean
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
```

## Users

`tools/downstream.py` reports one direct importer and 423 transitive downstream modules.
The only downstream module mentioning the theorem is the direct importer below. It already
explicitly imports every removed module, including CommAlgebraSheafModule and Equivalence,
so its public import closure and the import closure of all its downstream users are preserved.
No user requires adaptation. The import-pruning check is run by delivery preflight.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SheafAlgebrasDirectedColimit | none recorded | Same signature and import closure; it already imports all removed modules. |

## Status

landed 20261012T095926-L-325606 2026-10-12 (merge of deliver/U3/Sheaf.CategoryTheory.SheafAlgebrasDirectedColimitAlgebraCore)
