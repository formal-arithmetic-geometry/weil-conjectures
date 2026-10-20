## What changed

Completed the listed retirement repair for
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat`.
`deleted.txt` withdraws the Sheaf copy, and the existing flatness node now points
to `WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat`.
The mathematical statement, DAG proof, all incoming dependency edges and the
blueprint unit route are preserved.

The change record is
`coord/changes/G1-strict-henselization-structural-flat-retirement.md`.
It records the exact old and replacement signatures, every listed consumer,
and a complete Lean verification of their equivalence via
`smallStrictHenselizationColimitIso` over the base.

No active Lean module imports the copy. All four listed Sheaf consumers are
quarantined; their archives, rework entries, Lean attachments and dependencies
remain intact. Their four active source counterparts already import and apply
the upstream theorem. They were compiled verbatim through `lcompile.py`, with
no warnings: normalization finite 4.9 s, generic etale 2.5 s, purity data 4.4 s,
finite etale model 4.9 s. The compatibility check compiled in 3.0 s. Both the
source flatness theorem and its exact small-ring specialization print only
`propext`, `Classical.choice` and `Quot.sound`.

## Proved and sorry left

This assigned retirement repair started with 0 sorries and leaves 0 sorries.
No hole is counted as closed and no hole is added or split off.
`AlgebraicGeometry.Scheme.strictHenselization_structural_ringHom_flat` remains
proved in the adopted source module. The verification derives the original
small-ring statement from that proof, with no sorry.

## No longer needed

The duplicate module
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat` is retired.
Its four imports disappear with it:
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`,
`Mathlib.RingTheory.RingHom.Flat`,
`WeilConjectures.RingTheory.ProEtale.FaithfullyFlat`, and
`Mathlib.AlgebraicGeometry.Morphisms.Etale`.
Those tools may still be used by the source proof and other consumers; no claim
is made that their modules or DAG nodes can be removed. The flatness node and
all of its proof-dependency nodes remain needed and are preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not describe the current queue entry: this is an
explicit retirement repair, and the assigned file was already sorry-free.
The retirement row's four consumers are in quarantine, not the active Lean tree.
They have active upstream counterparts; absence of their Sheaf files is not a
withdrawal of their archived work.

The two strict henselization models are not definitionally equal. A blind import
rewrite would therefore be insufficient for an archived consumer restored with
its old signature. The change record supplies a compiled comparison over the
base and a proof transporting upstream flatness to exactly that signature.
The approved retirement request, current source consumers, and preserved archive
and DAG dependency records have all been checked together.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
