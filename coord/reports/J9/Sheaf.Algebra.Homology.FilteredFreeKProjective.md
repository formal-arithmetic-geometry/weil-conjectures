## What changed

Completed the assigned module's retirement in favour of its already proved upstream
twin `WeilConjectures.Algebra.Homology.FilteredFreeKProjective`. Withdrawn the redundant
Sheaf module using `deleted.txt` and redirected all three DAG Lean attachments to the
upstream module. Updated their proof origins and the telescope proof description to
match its direct conclusion. The three full signatures match byte for byte. No
source-library file, target, mathematical statement, or dependency list changes.

The change record is `coord/changes/J9-retire-filtered-free-kprojective.md`.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero split off, zero left.
All three declarations already have complete proofs in the preserved upstream module:
`CochainComplex.isKProjective_of_filtered_free_stage`
(`lem-pc-filtered-free-kprojective-stage`),
`CochainComplex.isKProjective_of_filtered_free_telescope`
(`lem-pc-filtered-free-kprojective-telescope`), and
`CochainComplex.isKProjective_of_filtered_free`
(`lem-pc-filtered-free-kprojective`).

`lcompile.py` compiled a scratch verification importing the upstream module; all three
`#print axioms` results contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
This is a duplicate retirement, not a new proof or a decomposition.

## No longer needed

Pruned `Sheaf.Algebra.Homology.FilteredFreeKProjective`. Its three public Mathlib
imports and two private upstream proof imports disappear with the redundant copy.
The replacement module retains those same dependencies and all three declarations.
No mathematical node or proof dependency is pruned: parent DAG nodes keep their
existing result, now attached to its upstream declaration.

There are no live or quarantined Lean importers to adapt. Both upstream base-derived
extension parents and `Sheaf.RingTheory.MarkedFiniteFreeLiftCompatibility` already
import the replacement. The unit route stays unchanged. The earlier blocker, the
Sheaf assembly twin, was retired by Y7 before this delivery.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open proof obligation, but the assigned file has
no holes and its actual queue row is a retirement. K6's previous delivery rewrote
already complete proofs without retiring the duplicate. The old retained-twins TSV
still describes the pre-Y7 assembly collision; the current source already uses the
upstream assembly. The three remaining DAG attachments were the outstanding repair.

Read Stacks `dga.tex`, `lemma-property-P-sequence` and
`lemma-property-P-K-projective` (Tags 09KL--09KM). The upstream proof keeps that same
finite-filtration and telescope argument, including the splitness assumptions,
universes, empty bases, zero ring, and unbounded complexes.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
