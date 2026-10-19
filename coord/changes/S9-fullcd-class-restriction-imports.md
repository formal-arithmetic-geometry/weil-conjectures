# Sheaf.Paper.FullCDClassRestriction imports

## Reason

The restriction proof uses the existing canonical comparison isomorphism from
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`, its inverse naturality equation,
and Mathlib's scheme pullback and weakly-etale base-change instances. It does not use
derived categories, the ringed-site presentation of modules, constructibility predicates,
or the support-site coherence theorem. Remove those four unused imports.

The two existing declaration signatures and the witness construction are unchanged.
No target statement or definition meaning changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
```

## New

These four import lines are removed. The existing public import of
`Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence` remains and supplies the canonical
comparison isomorphism used by both the witness definition and the new proof.

## Users

`tools/downstream.py Sheaf.Paper.FullCDClassRestriction` lists 172 transitive importers.
Only `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange` directly imports the item.
No external module mentions either of its declarations, as checked by whole-source `rg`.
The source-only `tools/import_prune_check.py` passes: no downstream module loses a
referenced declaration through these removals. No consumer file is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | not queried; no adaptation | Existing signatures remain; source import-pruning check passes. |

## Status

landed 20261019T112531-L-3951370 2026-10-19 (merge of deliver/S9/Sheaf.Paper.FullCDClassRestriction)
