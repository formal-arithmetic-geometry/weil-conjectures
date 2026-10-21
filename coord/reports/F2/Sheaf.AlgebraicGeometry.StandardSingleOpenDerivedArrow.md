## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleOpenDerivedArrow.lean` from the
quarantine path recorded in `coord/rework.tsv`. The archived file failed against the
current library because `derivedPullback` is already globally irreducible. Removed
only its redundant `[local irreducible]` attribute. The public theorem
`AlgebraicGeometry.standardSingle_open_derived_arrow`, its proof, all imports and its
existing DAG attachment are preserved.

The module compiles without warnings using `lcompile.py` against the current server
build and unchanged local copies of its two missing compiled dependencies. Those
copies were used only to produce sandbox build artifacts and are not delivery edits.
The proof still applies `restricted_base_change_compatibility`, proves the pinned
single comparison and coefficient naturality, and transports the coefficient from
open-site restriction to literal restriction. Its construction covers empty and top
opens with the same natural isomorphisms. The quarantined consumer
`StandardSingleOpenStalkArrow` still calls the identical theorem with the identical
arguments; no consumer adaptation is needed.

Change record: `coord/changes/F2-standard-single-open-derived-arrow-restore.md`.

## Proved and sorry left

This is a zero-hole restoration and compatibility repair. The archive contained zero
`sorry`, and the restored module contains zero. Holes closed: 0. Holes added: 0.
No statements were split off. `AlgebraicGeometry.standardSingle_open_derived_arrow`
retains its complete proof; its six private helper theorems are also fully proved.

## No longer needed

No imports, modules or nodes are pruned. The existing node
`lem-pc-standard-single-open-derived-arrow` and all its dependencies remain in place.
The local reducibility attribute for `derivedPullback` is redundant because the
definition already carries that global attribute.

LeanFinder returned underived restriction lemmas, Loogle confirmed
`Adjunction.homEquiv_naturality_left`, and the requested grep search found no exact
replacement. The library also has `schemeDerivedBaseChangeMap_naturality`; the
archived proof already proves precisely the required naturality locally, so this
restoration preserves its import route.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from `lean/` because it was quarantined after a cluster
restore, not because its mathematics was withdrawn. Its archive is already fully
proved. Its local attribute for `derivedPullback` predates the current irreducibility
API and causes the compiler error fixed here. No mathematical statement, target,
definition, DAG proof plan or unit route changes.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
