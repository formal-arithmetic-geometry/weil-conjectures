# affineModelCoherentObjectComparisons local proof transparency

## Reason

The parent proof must avoid unfolding the choice constructions of derived pullback
and its composition comparison during categorical transport. File-local irreducibility
keeps the proof within the single-file compile limit. Preflight conservatively treats
an added attribute command as an interface change and requires this record.
The attribute is local to the parent file and changes neither exported reducibility
nor any public declaration's type, body of a public definition, or visibility.
No downstream adaptation is needed. No target meaning changes or needs reopening.

## Old

Before the final theorem there was no local irreducibility command. The declarations
`AlgebraicGeometry.perfectHomComposition` and `AlgebraicGeometry.derivedPullback`
kept their imported reducibility while elaborating that theorem.

## New

The following command is inserted before the final theorem:

```lean
attribute [local irreducible] perfectHomComposition derivedPullback
```

All existing public signatures and definitions remain verbatim. The only new helper
in the parent is a private abbreviation packaging supplied coordinate data and a
proved natural identification of its localized tilde functor. The two new imports
are proof-only imports. The new modules have their own DAG nodes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons | U2 | Local elaboration control for the proof only. |
| Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels | unclaimed | Calls the unchanged existence theorem; no adaptation. |

`tools/downstream.py --uses exists_affineModelCoherentObjectComparisons` reports
only the parent and AffineModelComparisonOfBottomModels as textual users. All 440
transitive importers receive the same declarations and no local attribute. There
are no changed signatures to adapt, and no adapted modules in this delivery.

## Status

landed 20261014T084702-L-89554 2026-10-14 (merge of deliver/U2/Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons)
