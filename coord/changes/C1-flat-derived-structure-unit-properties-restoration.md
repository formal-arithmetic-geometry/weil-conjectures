# AlgebraicGeometry.flat_derived_structure_unit_properties

## Reason

Restore the module from the quarantine named in `coord/rework.tsv`. Its original
proof is complete, but its public signature uses `derivedPullback`, whose former
Sheaf compatibility module is now empty. Lean diagnoses that declaration as only
privately imported. Import the adopted implementation publicly.

## Old

The archived file `quarantine/Sheaf/AlgebraicGeometry/FlatDerivedStructureUnitProperties.lean`
contains:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

The restored file `lean/Sheaf/AlgebraicGeometry/FlatDerivedStructureUnitProperties.lean`
contains instead:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

This is the only source difference from the archive. Every declaration signature,
visibility, docstring, and proof body is unchanged. No mathematical statement or
definition changes, so no target meaning is changed or weakened. The existing
node retains its attachment, proof route and dependencies; only `lean.note` records
the restoration.

## Users

`tools/downstream.py` initially reports an unknown module because the item is
quarantined. The `--allow-missing` check reports zero live downstream modules and zero
uses; direct source searches agree; a separate quarantine search finds the parent below. The DAG parent
check also identifies `lem-sc-flat-derived-structure-unit` as retaining this item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties | C1 | Restored and repaired; unchanged public theorem and proof compile. |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit | unclaimed; quarantined | Same theorem and explicit canonical map remain available. Its independent restoration also needs its own public DerivedPullback import migrated; no edit is delivered here. |

The quarantined parent imports this item privately, so its own public signature
cannot obtain `derivedPullback` through that proof import. Its recorded compiler
error is `Unknown identifier derivedPullback`, with Lean suggesting the source
public import. This is pre-existing source migration work, not an adaptation forced
by a changed signature or definition in this packet. A scratch parent copy with
that import migrated compiled successfully in 9 seconds; it is not delivered.

## Status

landed 20261021T004817-L-1790061 2026-10-21 (merge of deliver/C1/Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties)
