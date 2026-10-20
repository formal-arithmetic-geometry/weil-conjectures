## What changed

Retire Sheaf.AlgebraicGeometry.DeterminantDualLocalFrames as explicitly listed in
coord/retire-items.tsv. Its node now points to the proved upstream theorem in
WeilConjectures.AlgebraicGeometry.DeterminantDualLocalFrames. Withdraw the copy via
deleted.txt. Adapt its sole direct consumer,
Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal, to obtain the official frames
and identify the exterior presheaves using the proved equality theorem. Preserve
its public signature and its determinant/basis argument. No upstream file changes.
The change record is coord/changes/retire-determinant-dual-local-frames.md.
The adapted consumer compiles through lcompile.py in 8.1 seconds, with no warnings.
A proved private recursor/cast identity removes the reflexive data transports from
the dependent presheaf rewrite; no new public statement is introduced.

## Proved and sorry left

The assigned item has zero holes before retirement and zero holes afterward.
Holes closed: none. Holes added: none. Split off: none.
AlgebraicGeometry.exterior_dual_local_frames remains proved in the official module;
AlgebraicGeometry.exterior_dual_pairing_app_bijective remains proved in its unchanged
statement. No sorry remains in the adapted consumer or the retired copy.
An independent scratch import compiled in 1.5 seconds and printed exactly the
allowed axioms (propext, Classical.choice, Quot.sound) for both public theorems.
The import-direction check also accepts the official frame import.

## No longer needed

Withdraw Sheaf.AlgebraicGeometry.DeterminantDualLocalFrames and remove its private
import from Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal. The official
WeilConjectures.AlgebraicGeometry.DeterminantDualLocalFrames replaces it.
For the frame node itself, remove the legacy exterior-sheaf and exterior-presheaf
comparison dependencies: its official proof uses the official constructions
directly. The consumer still needs lem-sc-exterior-sheaf-presheaf-upstream-comparison.
No mathematical frame node or unit step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The brief describes a generic proof assignment, but this item is the zero-hole
retirement explicitly recorded in coord/retire-items.tsv. The recently adapted
legacy proof was already complete; merely recompiling it would not perform the
retirement. The official and legacy theorem signatures differ in exterior
construction names, so replacing the import alone is insufficient. The consumer
must transport both the existential section bases and their wedge formulas.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
