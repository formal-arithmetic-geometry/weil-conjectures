# Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth

## Reason

Complete the explicitly assigned retirement under the human's Hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. M1's repair 8bdeee4c0a already moved
the sole listed consumer and DAG attachment to the official source declarations.
The remaining Sheaf wrapper has no declarations and no active Lean importers.

## Old

The entire wrapper was:

```lean
module

public import WeilConjectures.RingTheory.ResidueFieldProjectiveDimensionDepth

/-!
Compatibility import for the adopted source theorem. Its complete proof and mathematical
dependencies remain in the source module imported above.
-/
```

## New

Withdraw `lean/Sheaf/RingTheory/ResidueFieldProjectiveDimensionDepth.lean` through
`deleted.txt`. Consumers use the official module
`WeilConjectures.RingTheory.ResidueFieldProjectiveDimensionDepth`.
The existing node `lem-weil-pbc-residue-field-pd-le-depth` keeps that module, file,
declaration, and statement in its Lean attachment; its note records this retirement.
No upstream file, target statement, definition, or proof changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth | A4 | Retire unused compatibility wrapper. |
| Sheaf.RingTheory.ResidueFieldProjectiveDimension | unclaimed | Inventory's consumer already imports the official dimension module; compiled unchanged. |

There are no current direct or transitive Lean importers of the retired wrapper.
The official dimension module imports the official depth module and applies
`Ring.residueField_projectiveDimension_le_depth R h` with the categorical dimension
API. The DAG parent `lem-weil-pbc-residue-field-pd-le-krull-dimension` still depends
on the retained depth node. No DAG dependency is removed, and the unit route stays.

The unchanged listed consumer compiled through `lcompile.py --all` with no warnings.
A scratch import/application check compiled and printed exactly `propext`,
`Classical.choice`, and `Quot.sound` for both canonical residue-field bounds.
`tools/downstream.py` confirms zero modules downstream of the retired path.

## Status

landed 20261020T160748-L-3403675 2026-10-20 (merge of deliver/A4/Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth)
