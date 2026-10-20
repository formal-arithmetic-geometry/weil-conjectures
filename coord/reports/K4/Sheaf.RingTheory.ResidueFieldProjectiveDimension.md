## What changed

Completed the assigned retirement of the zero-hole compatibility module
`Sheaf.RingTheory.ResidueFieldProjectiveDimension`, using `deleted.txt`.
The complete theorem remains
`Ring.residueField_projectiveDimension_le_ringKrullDim` in
`WeilConjectures.RingTheory.ResidueFieldProjectiveDimension`.

Updated only the Lean note of
`lem-weil-pbc-residue-field-pd-le-krull-dimension` to document the retirement.
Its existing adopted attachment and statement remain verbatim; its proof,
proof dependencies, DAG parent, and unit route are retained. No upstream file
or target statement is edited.

Change record: `coord/changes/K4-retire-residue-field-projective-dimension.md`.

Verification: the actual adopted regular-local consumer compiled unchanged
without warnings in 1.3 seconds. A scratch application of the full theorem
compiled in 1.0 second; its axiom check lists only `propext`, `Classical.choice`,
and `Quot.sound`. The consumer's project import closure contains no Sheaf
modules or duplicate twin pair. Mathlib searches via msearch (LeanFinder,
Loogle, and grep) found no replacement needed: the complete adopted theorem
is the exact existing library result used here.

## Proved and sorry left

Assigned zero-hole retirement: proved 0 of 0 sorries; 0 holes closed,
0 holes added, 0 split off, and 0 holes left in the item. The wrapper declared
no constants. No new theorem or mathematical proof is claimed.

The retained adopted theorem
`Ring.residueField_projectiveDimension_le_ringKrullDim`
(node `lem-weil-pbc-residue-field-pd-le-krull-dimension`) has its complete proof
and only the three allowed axioms.

## No longer needed

Pruned module `Sheaf.RingTheory.ResidueFieldProjectiveDimension` and its
compatibility public import of
`WeilConjectures.RingTheory.ResidueFieldProjectiveDimension`.
The latter module itself remains needed and available directly to its parent.

No mathematical node or proof dependency is pruned. In particular, the depth
bound, depth-to-support-dimension bound, categorical dimension API, and
bounded-resolution bridge all remain in the adopted proof route. The DAG
parent still cites this mathematical node and imports its adopted module.
No DAG node or quarantine archive is deleted.

## Where the brief, the DAG or earlier work was wrong

This is a listed retirement with zero holes, rather than an unfinished proof.
The inventory's DIFFERENT classification and historical consumer reflect the
old minimum-valued dimension API. M1's landed rework already replaced that
copy by a pure reexport, and the historical Sheaf regular-local consumer has
also been retired. The current DAG attachments and adopted regular-local
proof already use the synchronized categorical projective-dimension API.
The remaining task was removal of the redundant import path, not another
proof or an API change. Live and quarantined importer searches and the DAG
parent check support that retirement.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
