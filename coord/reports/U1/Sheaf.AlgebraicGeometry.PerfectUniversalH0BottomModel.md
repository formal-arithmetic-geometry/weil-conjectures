## What changed

Restored Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel from its quarantine
archive, as required by its rework assignment. Replaced the retired Sheaf derived-pullback
and derived-open-homology imports by their adopted WeilConjectures counterparts.
Preserved the complete archived proof and every declaration signature. Made the mapped
kernel inclusion's monomorphism instance explicit, fixed the section universe of open
restriction functors to u, gave explicit types to the four factors of the derived
restriction comparison, and used definitional equality for evaluation of the zero map.

The module compiles cleanly through lcompile.py (21.1 seconds). An importing audit
compiled and #print axioms for perfect_universalH0_bottom_model reported exactly
propext, Classical.choice, Quot.sound. The proof still uses
the finite-free residue model, exact open restriction and its homology comparison,
local free trivializations, and Mathlib's square-matrix transpose injectivity. The
rank-zero, negative-degree, and empty-scheme cases remain covered by the original
proof. No new mathematics, arbitrary witnesses, public definitions, or nodes were added.

Change record: coord/changes/U1-perfect-universal-h0-bottom-model-restore.md.

## Proved and sorry left

This is a zero-hole migration repair, not a new hole closure. The quarantined baseline
and restored item both contain zero sorry occurrences. Holes closed: none (0 of 0).
Holes added: none. Split off: none. Sorries left in the delivery: none.
The theorem AlgebraicGeometry.Scheme.perfect_universalH0_bottom_model and its existing
private helpers retain complete proofs. No dependency module is delivered or changed.

## No longer needed

Removed imports of Sheaf.AlgebraicGeometry.DerivedPullback and
Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology, both already retired empty
modules, replacing them by the corresponding adopted upstream modules. No DAG
mathematical dependency is pruned: all five recorded proof dependencies remain
necessary and used. No module is withdrawn. The quarantined parent and its dependency
on this item are preserved.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it was quarantined during upstream migration,
not because its mathematics was withdrawn. Its archive already contains the full
proof, so the actual assignment is restoration and API repair with zero holes. The
recorded import collision is repaired; compiling then revealed the three additional
elaboration issues described above. The existing DAG proof accurately describes the
retained argument and needs no change. Searches with leanfinder, loogle and grep found
no replacement scheme-level theorem; the square-matrix step already uses the exact
Mathlib declarations recorded by its dependency node. tools/downstream.py does not
index quarantined items, so consumers were checked by searching lean/ and quarantine/.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
