## What changed

Repaired the quarantined `Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth` and its sole
quarantined consumer `Sheaf.RingTheory.ResidueFieldProjectiveDimension`. Both now publicly
import their already proved adopted source modules. This removes the obsolete global-dimension
import and the incompatible natural projective-dimension API without duplicating the source
constants. No source-library file was edited.

Reattached `lem-weil-pbc-residue-field-pd-le-depth` and
`lem-weil-pbc-residue-field-pd-le-krull-dimension` to their existing source declarations. Their
statements and mathematical proof routes remain; the proof records now explicitly include
the already proved bounded-resolution/categorical-dimension bridge. The nonzero residue
field makes categorical dimension equal to the old minimum resolution length.

Change record: `coord/changes/residue-field-depth-canonical-api-M1.md`.

Both delivered modules compile without warnings. A temporary consumer imported both restored
paths and applied both the depth inequality and the finite-resolution conclusion. The axiom
checks for both canonical theorems return only propext, Classical.choice and Quot.sound.

## Proved and sorry left

Assigned repair with zero holes in the archived module: 0 holes closed, 0 holes added, 0 left.
The restored consumer also has zero holes. No split-off statements or new nodes.

The complete existing proofs of `Ring.residueField_projectiveDimension_le_depth`
(node `lem-weil-pbc-residue-field-pd-le-depth`) and
`Ring.residueField_projectiveDimension_le_ringKrullDim`
(node `lem-weil-pbc-residue-field-pd-le-krull-dimension`) are available through the restored
imports and have only the three allowed axioms. This is an API/import repair, not a new
mathematical proof or a claim to close an existing sorry.

## No longer needed

The restored modules no longer directly import `Sheaf.RingTheory.GlobalDimension` (already
withdrawn), nor carry duplicate copies of the residue-field theorem proofs. The old consumer
no longer imports the Sheaf depth module privately; the canonical source consumer already
imports and uses the canonical source depth proof.

All minimal-resolution, last-minor, regular-sequence, depth, support-dimension and
bounded-resolution bridge dependencies remain needed by the adopted proofs. No mathematical
node or proof module is pruned; no quarantine archive or DAG node is deleted. The old import
paths remain usable as public compatibility imports.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole rework, not an unfinished theorem. Its quarantine row records the
post-sync collision of the two global-dimension definitions. After retirement of the old
Sheaf definitions, the archive also refers to the removed `ModuleCat.projectiveDimension`.
Both DAG Lean attachments still named the quarantined copies and their obsolete signatures.
The synchronized source already provides the complete corrected proofs. Keeping the old
proof copies would duplicate their public declaration names when combined with source
consumers; reexporting and reattaching avoids that collision.

The consumer archive likewise depended on the old minimum-valued API, so it is repaired in
the same packet. The natural mathematical statements and unit route are unchanged.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
