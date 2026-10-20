## What changed

Retired Sheaf.RingTheory.GradedKernelInternal, as listed in coord/retire-items.tsv,
in favor of WeilConjectures.RingTheory.GradedKernelInternal. Reattached
lem-sc-p1-graded-kernel-internal to the existing proved theorem
MvPolynomial.graded_kernel_internal_finite and recorded its exact signature.
The upstream conclusion is identical and omits only the unused hsmulM and hq
hypotheses. The old signature is checked by direct application in a scratch
Lean theorem. The upstream source remains unchanged. Validation through lcompile.py:
the original signature derived from upstream compiles (exit 0, 1.1 seconds),
and both that theorem and the adopted theorem print only propext,
Classical.choice and Quot.sound. The unchanged upstream GradedSyzygy consumer
also compiles (exit 0, 2.7 seconds).

Corrected proof step 1 to mention finite homogeneous generators of F only:
the existing proof never needs a generating family for M. The remaining proof
steps, proof dependencies, mathematical statement and unit route are preserved.
Change record: coord/changes/Q3-retire-graded-kernel-internal.md.

## Proved and sorry left

Actual baseline: zero sorries in the current item, despite the stale retirement
table's count of one. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains in the item or is introduced anywhere by this delivery.

MvPolynomial.graded_kernel_internal_finite is already completely proved in the
adopted upstream module. This delivery is duplicate retirement, not new proof
progress or decomposition. The original Sheaf statement follows from that
upstream theorem without an extra hypothesis. The private helper
finite_homogeneous_spanning also duplicates the upstream module's private helper.

## No longer needed

Pruned module: Sheaf.RingTheory.GradedKernelInternal. Its public Mathlib imports
and private proof imports disappear with the duplicate. The mathematical nodes
lem-sc-p1-finite-homogeneous-generators and lem-sc-p1-graded-kernel-finite remain
needed by the adopted proof; neither is claimed as pruned.

There are no current Lean importers of the withdrawn module, including in
quarantine. The former Sheaf.RingTheory.GradedSyzygy consumer is already retired.
The existing WeilConjectures.RingTheory.GradedSyzygy imports the upstream theorem
and calls it twice. The DAG parent's references to the kernel node are preserved
and now resolve through the upstream attachment. No further node is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief and retirement census describe an old hole count; the
live module is already fully proved. This packet performs the listed retirement
rather than claiming to close a nonexistent hole. The upstream theorem has the
same conclusion with two unused hypotheses removed. The DAG proof's first step
incorrectly mentioned taking a generating family for M; the actual proof only
takes one for F. The node's mathematical statement remains unchanged.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
