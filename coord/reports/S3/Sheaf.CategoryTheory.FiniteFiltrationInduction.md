## What changed

Retired the duplicate Sheaf.CategoryTheory.FiniteFiltrationInduction and migrated
all twelve current direct consumers to the identical proved API in
WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension. Public and
proof import visibility is preserved. The finite-filtration node now attaches to
that replacement. No upstream source file is changed.

Repair of returned head 6593810f0e: retained FilteredPageTwoComparison with its
complete original proof and migrated import. Both its live and quarantine paths,
its rework row and its claim are absent on the current base and on the server.
The pre-removal source is preserved in the returned delivery's parent; comparison
shows exactly one changed import. Restored its corresponding DAG node from that
same parent, retaining its statement, proof, dependencies and original blueprint
route. Delivery creation metadata identifies this restoration; no old approval
is carried forward. No available rework item exists to claim.

Rebased every existing adapted source on the current tree, and added the newly
restored direct consumer Sheaf.Paper.FlatFilteredComplexComparison with only the
same import migration. The thirteen delivered modules compile together on the
server through lcompile.py --all. The declaration sections of the retired module
and upstream replacement are identical.

Change record: coord/changes/FiniteFiltrationInduction-official-retirement.md.

## Proved and sorry left

Assigned module: zero holes before and after; proved 0 of 0 sorries; holes added:
none; split off: none. This is a zero-hole duplicate retirement and restoration.
CategoryTheory.FilteredObject.exists_gradedMap_steps and
CategoryTheory.FilteredObject.finite_filtration_induction_steps retain their
complete proofs in the replacement. The restored
CategoryTheory.filteredPageTwoModel_comparison is completely proved with no hole.

Two existing consumer holes remain unchanged:
- CategoryTheory.exists_boundedAbove_rhom_hyperExt
  (lem-per-bounded-above-rhom-hyperext; BoundedAboveRHomHyperExt).
- CategoryTheory.finite_filtered_colimit_model
  (lem-weil-pbc-finite-filtered-colimit-model; FiniteFilteredColimitModel).

## No longer needed

Pruned module: Sheaf.CategoryTheory.FiniteFiltrationInduction. Its eleven active
direct consumers and the restored FilteredPageTwoComparison now import the
upstream replacement instead. No mathematical node, proof dependency or unit
route is pruned. lem-sp-finite-filtration-induction, def-sp-filtration and
lem-weil-pbc-short-five-lemma remain needed. Quarantined parents and their
attachments are preserved. The active FilteredHomotopySpectralSequence source is also a
rework archive; only its deleted-module import is changed. restoration must migrate any remaining duplicate
import. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The assigned module has no holes; its requested repair is duplicate retirement.
The retirement inventory names FiniteFiltrationInduction, but the actual exact
replacement is FiniteFiltrationInductionExtension.

The latest return describes FilteredPageTwoComparison as quarantined. On this
base neither its source nor its node nor its quarantine row survives the batch
removal. Restoring only the source fails the new-module attachment check, so this
repair also restores its original node and all dependencies. No weaker statement
or empty replacement is substituted.

## New nodes

Restored lem-sp-filtered-page-two-comparison at its original path
 dag/nodes/sec-picard-framework/lem-sp-filtered-page-two-comparison.json.
Its mathematical content and complete Lean proof are those of the former G9
landing, preserved in the parent of returned head 6593810f0e; the sole Lean change
is the import migration. This is an archival restoration, not a new split or
an added hole. Independent review is required.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
