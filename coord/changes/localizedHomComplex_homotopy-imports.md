# localizedHomComplex_homotopy imports

## Reason

The degree-zero comparison uses no filtered colimits or homology of complexes in
the sheaf category itself. Remove the unused public imports of
Mathlib.Algebra.Category.Grp.FilteredColimits and
Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian. The Hom-complex import already
provides the sheaf-module preadditive structure; cycles and homology in this
statement are taken only in AddCommGrpCat. All existing declaration
signatures and definitions remain byte for byte unchanged. This is an explicit
public-import removal, to be read with the delivery; no target meaning changes.
The two new proof-dependency imports are plain imports.

## Old

```lean
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
```

## New

Both lines are removed; no replacement is needed. The module continues to import
Mathlib.Algebra.Category.Grp.Abelian for the section complex's homology.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.LocalizedHomComplexHomotopy --uses
localizedHomComplex_homotopy` lists one other declaration user, below. It also
lists 321 transitive module importers. Only RhomIntoKInjectiveLocal directly
imports this module, using a plain import; that import does not expose this
module's imports to its own downstream clients. It already publicly imports both Mathlib.Algebra.Category.Grp.FilteredColimits
and Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian itself.
Its own public imports provide the required category and group instances, and its original source is checked
against the changed compiled module. No other module is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal | not held in this delivery | Signature and proof unchanged; original compiles against the new module. |

## Status

landed 20261012T135301-L-1684750 2026-10-12 (merge of deliver/P3/Sheaf.Algebra.Homology.LocalizedHomComplexHomotopy)
