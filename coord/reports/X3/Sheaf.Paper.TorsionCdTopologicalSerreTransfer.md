## What changed

Replaced the sorry in
`AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes`
with a weak-Serre-minimality argument. Intersect the original hull with objects
whose ordinary derived sections vanish above d+2. The existing finite-complex
heart estimate bounds the generators. Long exact sequences give extension
closure. Finite partial sums and the existing filtered-continuity theorem give
small coproduct closure. A new bounded-kernel step gives kernel closure; two
short exact sequences through the coimage then give cokernel closure.

Added the proof-only imports for these estimates and categorical APIs, and the
new module `Sheaf.Paper.TorsionCdBoundedSerreKernel`. No existing signature,
definition, public import, target, or source-library file changes. The previously
proved finite-coefficient branch is preserved verbatim. Updated the main node's
proof, proof dependencies and proof origin to describe the actual reduction.

## Proved and sorry left

Closed the one original hole, by declaration name:
`AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes`
(node `lem-sfb-torsion-cd-topological-serre-transfer`). Its assembly proof contains
no sorry. It uses the existing finite-heart estimate and filtered continuity,
plus the new kernel obligation below. The finite-coefficient theorem was already
proved in the base and is not counted as a newly closed hole.

Added one hole:
`AlgebraicGeometry.ProEtale.torsionCd_bounded_serre_kernel`
(node `lem-sfb-torsion-cd-bounded-serre-kernel`). It says that the kernel of a map
between two hull objects, each separately assumed bounded above d+2, retains that
bound. This is precisely the kernel-closure step; it does not assert the original
bound for arbitrary hull objects. The cokernel, extension, coproduct and minimality
steps are implemented in the main module, rather than included as hypotheses of
this new theorem.

Counts: original module 1 hole to 0; new modules 1 hole; net 0. This is a
decomposition, not a complete proof of the arbitrary-affine geometric assertion.
No hollow definitions, new axioms, or arbitrary data witnesses are introduced.

Both delivered modules compiled together with lcompile.py. The only initial
successful-compile warning was a long line, now shortened; the final compile and
delivery checks provide validation of the final text.

## No longer needed

The main proof no longer needs
`lem-sfb-finite-complex-heart-filtered-approximation`
(`Sheaf.Paper.FiniteComplexHeartFilteredApproximation`) or
`lem-sfb-noetherian-torsion-cd-topological-serre-transfer`
(`Sheaf.Paper.NoetherianTorsionCdTopologicalSerreTransfer`). It does not use a
Noetherian approximation or assume that every hull object is an ind-finite heart.
These nodes and modules are not withdrawn: their valid restricted statements
remain available to other consumers. Their proof-dependency edges from the main
node are removed.

The local node `lem-sfb-finite-coefficient-serre-cd` remains realized and proved in
the same module, but is not a step of the new uniform proof; its main-node proof
edge is removed. Its private proof imports remain necessary for that theorem.
No existing Lean import is removed and no module is deleted. The finite-heart
estimate and filtered-continuity nodes remain needed. The blueprint unit and its
realized route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original DAG route calls the finite-heart approximation without
Noetherianity, but that lemma has been repaired to require Noetherianity after a
Stone-Cech counterexample. Consequently it cannot be applied to this theorem's
arbitrary affine X. This is a defect of the old structural argument, not a
counterexample to the cohomological conclusion. The new reduction does not claim
that false approximation.

STATEMENT-DISPUTED: the arbitrary-affine bounded-kernel input remains an unresolved
geometric assertion. The existing finite-model image results and triangle closure
alone do not establish it for arbitrary maps between previously generated hull
objects. HRS Section 8, (8.1) and Lemma 8.6 do not state it in this generality.
The new node records the actual relation-resolution obligation and explicitly
marks the missing comparison; no completeness of arbitrary kernels is assumed.
The kernel lemma has been checked against zero maps, isomorphisms, zero rings and
empty schemes: it reduces to an input bound or zero in those cases. Finite
discrete coefficients have the stronger established bound above d.

## New nodes

`lem-sfb-torsion-cd-bounded-serre-kernel` in
`dag/nodes/sec-six-functors-basics/lem-sfb-torsion-cd-bounded-serre-kernel.json`,
realized by `Sheaf.Paper.TorsionCdBoundedSerreKernel` and the theorem
`AlgebraicGeometry.ProEtale.torsionCd_bounded_serre_kernel`. This isolates only the
kernel step between objects already satisfying the bound. Its source is the
coefficient-transfer obligation in the latest blueprint refinement proof (2),
with the arbitrary-map relation-resolution step already identified in
`lem-sfb-weak-serre-supported-derived-generation`. An exact reference for the
unresolved full-generality geometric comparison remains WANTED. Three genuine
Mathlib searches are recorded in the node. There is no statement/interface repair
and therefore no change record or forced consumer adaptation.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
