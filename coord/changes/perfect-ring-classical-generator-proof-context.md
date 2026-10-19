# DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton

## Reason

The proof uses limit and pretriangulated notation. The static interface checker classifies
the added namespace openings as an interface change. They affect elaboration in this file
only. No public declaration's signature, visibility, definition, instance or attribute
changes. All existing public imports remain identical. The added import of
`WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatTelescope` is proof-only.

## Old

```lean
open CategoryTheory
```

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
```

The public theorem retains its verbatim explicit binders, including the independent
localization universe `w`. Helper theorems are private, and all added instances are local to proofs.
Opening namespaces introduces no declaration or instance.

## Users

`tools/downstream.py Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
--uses isPerfectRingComplex_eq_triangEnvelope_singleton` and textual searches identify the
following declaration users. No consumer adaptation or target statement review is needed
because no definition or statement changed; transitive importers see the same interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator | A5 | Proves the existing theorem and adds namespace openings. |
| Sheaf.CategoryTheory.DerivedCategory.PerfectOverDerivedCompleteRing | unclaimed | Its use of this equality has the same signature and meaning. |
| Sheaf.CategoryTheory.Triangulated.GeneratingClassDetermination | unclaimed | Both uses of this equality retain their signatures and meaning. |

## Status

landed 20261019T231028-L-540551 2026-10-19 (merge of deliver/A5/Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator)
