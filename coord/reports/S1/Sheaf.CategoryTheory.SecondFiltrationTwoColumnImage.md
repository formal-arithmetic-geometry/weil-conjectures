## What changed

Restored lean/Sheaf/CategoryTheory/SecondFiltrationTwoColumnImage.lean from its
quarantine archive. Replaced its public Sheaf.CategoryTheory.DoubleComplexTotal import
with public WeilConjectures.CategoryTheory.DoubleComplexTotal, matching the adopted
row-comparison dependencies and repairing the reproduced duplicate-filtration import
failure. Every declaration and proof body is otherwise unchanged. Preserved the node's
Lean attachment and dependency route; appended a repair note to proof_origin.

The archived module fails immediately on the duplicate IsExhaustive declaration.
The repaired module compiles through lcompile.py in 9.2 seconds with no warnings.
An additional 8.5-second compile with #print axioms confirms that the theorem uses
only propext, Classical.choice and Quot.sound.
The change record is coord/changes/s1-second-filtration-two-column-image-import.md.

## Proved and sorry left

This is a zero-hole rework repair, not a new proof or decomposition.
CategoryTheory.secondFiltration_two_column_image and all its private helpers already
have complete proofs in the archive and remain complete. Holes closed: 0 of 0.
Holes added: 0. Sorries left in the delivery: none. No statements split off.
The existing node is lem-sp-second-filtration-two-column-image.

## No longer needed

Removed the duplicate import Sheaf.CategoryTheory.DoubleComplexTotal from this module;
its role is supplied by WeilConjectures.CategoryTheory.DoubleComplexTotal. No mathematical
node or module is withdrawn: the diagonal-filtration definitions and every existing
proof dependency remain needed. No deletion manifest is supplied and the quarantine
archive is untouched.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because it is quarantined, not because its
statement was withdrawn. Its archive contains zero sorry, so this delivery repairs
its import interface rather than claiming to close a proof hole. The recorded import
collision was reproduced before the repair. No mathematical statement or unit route
needed correction. The quarantined parent CartanEilenbergComparisonIndependence still
uses this theorem and is preserved; zero current importers does not justify withdrawal.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
