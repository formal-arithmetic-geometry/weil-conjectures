# strictHenselian_cohomology_locally_zero proof commands

## Reason

The completed proof introduces a private general lemma for preservation of filtered
colimits, whose universes are v and w, and uses the OpenNhds notation. The static interface
check conservatively flags the extra universe names and the open command. These commands
do not alter any exported declaration's elaborated type, definition or instance. The
original theorem keeps its original signature, including its anonymous Ext universe.

## Old

```lean
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
```

## New

```lean
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
```

The two additional universe names occur only in a proved private helper. The names opened
by `open TopologicalSpace` are used only in the theorem's proof. The module header, public
imports and public section retain their original forms.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.StrictHenselianCohomologyLocallyZero | R3 | Private helper and proof commands added; public theorem type unchanged. |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | not determined by this worker | Its use of strictHenselian_cohomology_locally_zero remains valid without adaptation. |

The change introduces no public declaration or changed signature in this existing module.
No target statement or definition used by a target changes. The command-only difference
has no declaration name for downstream.py --uses to search. Its sole direct importer is
listed for the reader; it needs no adaptation.

## Status

landed 20261012T135312-L-1690456 2026-10-12 (merge of deliver/R3/Sheaf.Paper.StrictHenselianCohomologyLocallyZero)
