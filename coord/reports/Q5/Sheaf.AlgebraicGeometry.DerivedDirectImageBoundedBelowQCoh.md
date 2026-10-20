## What changed

Retired `Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`, the duplicate
assigned in `coord/retire-items.tsv`. Its public theorem
`AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh_of_isGE` is already proved
with the identical signature in the upstream twin
`WeilConjectures.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`.
Reattached node `lem-pc-derived-direct-image-bounded-below-qcoh` to that declaration.
The file is withdrawn through `deleted.txt`. No upstream file is changed.

There are no current Lean importers of the copy, including quarantined files. The
row's former consumer `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh` is
already absent; its node points to the upstream module, which already imports the
upstream bounded-below theorem. Thus no consumer edits are necessary. This is the
reviewed retirement route, retaining the bounded-below step and the parent's use
of it rather than discarding an unfinished dependency.

Validation: the original copy compiled cleanly (18.7 seconds). A probe importing
only the upstream twin checked the full theorem type and printed its axioms:
`propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx` (2.3 seconds).
The current upstream parent separately compiled cleanly through `lcompile.py`
(39.4 seconds).
Source import-closure scans found zero Sheaf/upstream twin pairs in the upstream
theorem's 413-module closure and the parent's 527-module closure; neither reaches
the retired copy. The parent DAG citation and unit route remain intact.

## Proved and sorry left

This is a retirement repair with zero original holes: 0 closed, 0 added, 0 split
off, and no remaining sorry in any delivered Lean source. The retained upstream
`AlgebraicGeometry.schemeDerivedDirectImage_preserves_QCoh_of_isGE` is already
proved and has only the three permitted axioms. No proof is replaced by a hole.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`.
Its private `qcoh_containsZero`, `qcoh_pages`, and `property_of_filtration` helpers
are local duplicates; the upstream proof contains its own complete helpers.
The withdrawn file's four public imports and five proof imports disappear with
it. No consumer import is removed or added, since there are no current importers.
No mathematical node is pruned: the bounded-below node and all seven of its proof
dependencies remain, now realized through the upstream theorem. No further module
is claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described a module with a hole, but the current copy is
already proved. The actual listed assignment is the human-authorized retirement
in `coord/retire-items.tsv` and `coord/changes/retire-sheaf-twins-20261020.md`.
Its recorded former consumer and prerequisite retirement list predate the current
tree. The parent has already migrated, and its dependency is preserved by
reattaching this node to the upstream theorem. The DAG theorem statement and its
proof route need no correction.

Change record: `coord/changes/retire-derived-direct-image-bounded-below-qcoh-Q5.md`.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
