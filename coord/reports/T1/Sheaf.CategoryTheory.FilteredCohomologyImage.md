## What changed

Completed the assigned retirement of `Sheaf.CategoryTheory.FilteredCohomologyImage`.
Switched all five remaining direct consumers to the upstream twin and replaced the duplicate
filtration name `cohomologyImage` by upstream `homologyFiltration`. Kept every consumer proof
complete. Updated the finiteness node's attachment and the four affected consumer statement
records; all mathematical statements, dependencies, and blueprint unit steps remain intact.
The change record `coord/changes/retire-filtered-cohomology-image-T1.md` enumerates
every downstream user and explains the replacement.

All five adapted modules compile cleanly (1.0–2.4 seconds each). A separate compiled check
proves by `rfl` that the full original filtration construction equals `homologyFiltration`,
and verifies its step formula. Source import-closure checks find no pair of nonempty twins
in any migrated consumer's environment. The two remaining downstream paper modules are
validated verbatim against the migrated consumers (18.8 and 14.2 seconds).

## Proved and sorry left

Repair/retirement with zero holes: proved 0 of 0 sorries; added 0; split off 0; left 0.
The existing proved `CategoryTheory.DecreasingFiltration.cohomologyImage_isFinite`
is supplied by `WeilConjectures.CategoryTheory.FilteredCohomologyImage`.
The complete proofs of `cohomologyImage_cycle_map`, `cohomologyImage_graded_normalized`,
`cohomologyImage_graded_presentation`, `stableSubquotient_at_bounds`, and
`filteredStationary_cycle_comparison` are preserved with the upstream filtration name.
This is a duplicate retirement, not a new mathematical proof or a decomposition.

## No longer needed

Pruned module: `Sheaf.CategoryTheory.FilteredCohomologyImage`, listed in `deleted.txt`.
Removed all five direct imports of that copy and replaced them with the upstream twin.
Its duplicate `CategoryTheory.DecreasingFiltration.cohomologyImage` construction and private
`complexStep_antitone` proof are unnecessary. The upstream module already proves finiteness
of precisely the same image filtration.
No mathematical node is pruned: `lem-sp-filtered-cohomology-image-finite` remains attached
to the upstream theorem, retaining its dependencies and all parents. Its former proof imports
remain available through the upstream twin; the consumer proof-dependency imports are retained.
The other four image-comparison modules and stationary comparison remain needed by their users.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an unfinished proof, but this item is a zero-hole retirement in
`coord/retire-items.tsv`. The stated API difference is resolved by the existing upstream
`homologyFiltration`, definitionally equal to the copy's `cohomologyImage`.
The retirement row lists seven direct consumers; five are live and two are quarantined
rework archives (`CartanEilenbergComparisonIndependence`, `FilteredHomotopySpectralSequence`).
Both archives and their Lean/DAG attachments are preserved. The change record gives their
exact paths and API replacement for restoration; their mathematics remains needed, and its
node now resolves to the upstream theorem. The live downstream closure has seven modules,
including two paper modules that need no edit.
No quarantined source is deleted, no source-library declaration changes, no target signature
changes, and no previously complete proof is replaced by a hole.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
