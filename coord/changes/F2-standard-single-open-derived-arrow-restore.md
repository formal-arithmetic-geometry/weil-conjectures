# AlgebraicGeometry.standardSingle_open_derived_arrow

## Reason

Restore the quarantined module assigned by `coord/rework.tsv`. The original archive
fails to compile because `derivedPullback` is already globally irreducible. Lean
rejects assigning that attribute again locally. Removing the redundant local entry
retains the intended reducibility behavior and the complete existing proof.

## Old

The module exists only at
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleOpenDerivedArrow.lean`.
Its local attribute command is:

```lean
attribute [local irreducible] derivedPullback
  Scheme.Modules.tensorPullbackObj
  schemeDerivedBaseChangeMap Scheme.picardTermwiseSingleMap
```

## New

Restore the archive to
`lean/Sheaf/AlgebraicGeometry/StandardSingleOpenDerivedArrow.lean`, changing only that
command to:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullbackObj
  schemeDerivedBaseChangeMap Scheme.picardTermwiseSingleMap
```

Every declaration signature and proof, all public imports, and the existing DAG Lean
attachment are identical to the archive. This changes no definition or statement.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow | quarantined | Its existing call to `standardSingle_open_derived_arrow p M g S V hVS` has the identical public signature; no adaptation. |

The current live Lean tree has no importer of this quarantined module. Its existing
DAG parent `lem-pc-standard-single-open-stalk-arrow` is retained. No targets need a
statement re-review because no definition or signature is changed.

## Status

landed 20261021T002135-L-1491016 2026-10-21 (merge of deliver/F2/Sheaf.AlgebraicGeometry.StandardSingleOpenDerivedArrow)
