## What changed

Completed the assigned retirement of Sheaf.RingTheory.GradedKernelFinite. The
upstream MvPolynomial.graded_kernel_finite already proves the same result with
three unused assumptions removed. Withdraw the duplicate through deleted.txt,
redirect the single remaining consumer Sheaf.RingTheory.GradedKernelInternal to
WeilConjectures.RingTheory.GradedKernelFinite, and remove those arguments at its
one call. All consumer signatures, visibility and public imports are unchanged.
Reattach lem-sc-p1-graded-kernel-finite to the existing upstream declaration and
record the interface migration in coord/changes/retire-graded-kernel-finite.md.

## Proved and sorry left

The assigned module started with zero holes. Holes closed: none (0 of 0).
Holes added: none. No sorry remains in the retired module or the adapted consumer.
The existing upstream theorem and adapted consumer both have complete proofs;
this delivery claims duplicate retirement, not a new proof or decomposition.
Validation: the adapted consumer compiles with lcompile.py in 3.4 seconds,
without warnings. The declaration diff reports no changed signatures or holes.
downstream.py confirms the only consumer; import_direction.py accepts the new
import. The delivery preflight also checks declarations and axiom probes.

## No longer needed

Retire Sheaf.RingTheory.GradedKernelFinite and remove its only remaining proof
import, in Sheaf.RingTheory.GradedKernelInternal. Use the existing upstream module
instead. Retain lem-sc-p1-graded-kernel-finite and its proof dependency
lem-sc-p1-graded-submodule-finite: the upstream proof uses both argument steps.
No mathematical result or unit step is pruned. The listed second consumer,
Sheaf.RingTheory.GradedNakayamaFree, was already retired on the current base.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief names a module that already has zero sorry. The current
queue and coord/retire-items.tsv instead assign its duplicate retirement. The
DAG still attached its theorem to the obsolete Sheaf copy. The upstream theorem
has the same conclusion and drops only unused assumptions, so no statement
correction, new mathematical node or source-library modification is required.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
