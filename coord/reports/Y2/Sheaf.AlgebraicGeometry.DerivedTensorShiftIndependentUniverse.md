## What changed

Completed the retirement item listed in `coord/retire-items.tsv`. Withdrew
`Sheaf.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse` through `deleted.txt`.
Its upstream twin publicly imports the full construction in
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`.

Adapted the five existing consumers that use the deleted namespace:
`SchemeCanonicalTensorShift` (public import and final construction name),
`SchemeCanonicalTensorShiftProperties`, `SchemeCanonicalTensorShiftRightUnitor`,
`SchemeTensorShiftBinaryLocalizationSquare` (private proof namespace openings),
and `SchemeTensorShiftLocalizationNormalization` (private `liftingIsoHom` reference).
All five are under `Sheaf.AlgebraicGeometry` and were unclaimed. All theorem
signatures and existing proofs are preserved. Two modules also have existing
local-instance declarations wrapped to comply with the 100-character limit.

Reattached `lem-sc-derived-tensor-shift-independent-universe` to the upstream twin,
declaration `DerivedCategory.commShift₂CurriedTensor`. Its statement, proof route,
and dependencies are unchanged. No upstream file or target statement was edited.

A sandbox-only compatibility probe proves by `rfl` that the old and upstream
`commShift₂CurriedTensor` data are equal, and likewise for `liftingIsoHom`, with
arbitrary independent universes. The upstream declarations' axiom lists contain
only `propext`, `Classical.choice`, and `Quot.sound`. A source import-closure
comparison removes only the retired copy and adds only the upstream wrapper; no
additional duplicate implementation modules enter any consumer through this change.

Validation: all five adapted modules compile against the upstream construction;
all eight other downstream modules reported by `tools/downstream.py` also compile
against the sandbox overlay. The unchanged `SchemeCanonicalTensorShiftAssociator`
has a pre-existing long-line warning and is not included in the packet. The five
adapted modules have no long lines or holes. Declaration comparison reports no
changed signature in any adapted module. The delivery dry run compiles the set
and passes preflight (CODEX). Its consumer axiom probes for
`SchemeCanonicalTensorShiftProperties` and `SchemeTensorShiftBinaryLocalizationSquare`
timed out at 60 seconds; the tool explicitly accepts these as notes and repeats the
probes at merge. The direct upstream-construction axiom checks completed successfully.

Change record: `coord/changes/Y2-retire-derived-tensor-shift-independent-universe.md`.

## Proved and sorry left

This is a zero-hole retirement repair: the item had 0 `sorry`s and the replacement
has 0. Holes closed: none. Holes added: none. Split-off statements: none. Every
adapted consumer is sorry-free; every existing proof is retained. The item is
completed by retiring its duplicate implementation and adapting all its users,
not by claiming a new proof of an already proved declaration.

## No longer needed

The entire module `Sheaf.AlgebraicGeometry.DerivedTensorShiftIndependentUniverse`
and its duplicate namespace implementation are no longer needed. Its only direct
importer, `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift`, now imports the
upstream twin. All five declaration users now use the upstream API.

No mathematical dependency is pruned: the same localization and K-flat proof
construction is already supplied by upstream. The existing node remains and points
at upstream. The retired copy's two public imports are already publicly imported
by `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`, which the direct
consumer imports, so their visibility is retained.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief describes proof work in general, but this queue row is explicitly
kind `retire`, with zero holes. The retirement instructions in
`coord/changes/retire-sheaf-twins-20261020.md` apply. The API-difference note says
the twin lacks `L`, `LKFlat`, `F`, `liftingIsoHom`, and `lifting`; those declarations
are all present in its public import, under `DerivedCategory.TensorCommShift₂`.
The upstream construction now separates the universes, so the original reason for
the duplicate is obsolete. No mathematical statement or unit route needed repair.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
