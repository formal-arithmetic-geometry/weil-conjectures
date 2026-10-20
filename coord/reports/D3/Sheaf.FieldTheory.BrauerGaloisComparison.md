## What changed

Completed the listed retirement of Sheaf.FieldTheory.BrauerGaloisComparison.
Withdrawn its unused Field.nonempty_equiv_brauerGroup_galoisUnitsH2 wrapper and
redirected lem-sc-brauer-galois-units-comparison to the actual upstream equivalence
Field.brauerGroupEquivGaloisUnitsH2. The node proof now names the upstream construction's
helpers; its statement and dependencies are unchanged. No consumer needs adaptation:
downstream.py and a separate source scan found zero importers or external name uses.

Verified the old statement from the upstream equivalence by compiling
`exact ⟨Field.brauerGroupEquivGaloisUnitsH2 K⟩` for arbitrary fields and universe u
(1.4 seconds). Its axiom audit reports only propext, Classical.choice and Quot.sound.
The original local module also compiled (2.8 seconds). These verification files were
removed before delivery, as this packet retires the wrapper rather than retaining it.

Change record: coord/changes/retire-brauer-galois-comparison-d3.md.

## Proved and sorry left

Actual initial hole count: zero. Holes closed: zero of zero. Holes added: zero.
No sorry remains or is introduced by this delivery. The removed theorem
Field.nonempty_equiv_brauerGroup_galoisUnitsH2 was already proved; this is a retirement,
not a new mathematical proof. The upstream equivalence realizing the node is complete
and its transitive axiom audit has no sorryAx. No statements were split off.

## No longer needed

Pruned module: Sheaf.FieldTheory.BrauerGaloisComparison, including its sole declaration
Field.nonempty_equiv_brauerGroup_galoisUnitsH2. Its six import lines disappear with it:
Mathlib.Algebra.BrauerGroup.Defs, WeilConjectures.FieldTheory.GaloisUnitsCohomology,
WeilConjectures.Algebra.Central.ReducedNorm,
WeilConjectures.FieldTheory.BrauerScalarDefectExists,
WeilConjectures.FieldTheory.BrauerScalarDefectFaithful, and
WeilConjectures.FieldTheory.BrauerScalarDefectSurjective.
Those imported modules and the scalar-defect proof nodes are still used by the upstream
construction and are not claimed as globally pruned. The comparison node remains,
attached to the upstream equivalence. No unit-route step is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not describe the current queue classification:
this is a retire item with zero holes and zero consumers, as coord/retire-items.tsv
records. The stale DAG attachment names the local Nonempty wrapper even though the
upstream twin now constructs the equivalence itself. The actual equivalence realizes
the same mathematical statement without any hypotheses added or conclusion weakened.
The human retirement hand-off, rather than a new split, is applied here.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
