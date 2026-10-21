## What changed

Filled the proof of `CategoryTheory.weakSerre_bounded_homology_thick` in
`Sheaf.CategoryTheory.WeakSerreBoundedThick`. Its statement, universes, docstrings,
and imports are unchanged. The proof follows the five steps of
`lem-sfb-weak-serre-bounded-thick` and Stacks Tag 06UQ.

Triangulated closure is the bounded-intersection clause of
`CategoryTheory.cohomology_in_weak_serre_subcategory`. A local proved calculation
constructs the isomorphism from a retract to the kernel of one minus its
idempotent: its forward map is the kernel lift of the inclusion and its inverse
is the kernel inclusion followed by the retraction. Both inverse identities and
the required normalization are proved explicitly. Kernel closure and
isomorphism closure then put each retract homology object in the weak Serre
class. The existing interval-concentration retract API transfers boundedness.
Finally, applying homology to the retract and using the zero identity criterion
proves preservation of every specified interval directly.

Read the assigned node, all declared dependency statements and their Lean
interfaces, the Brown unit record, and the cited Stacks proofs. LeanFinder,
Loogle and Mathlib/source/project searches found no public theorem giving the
whole assertion; existing private proofs in `CoefficientHeartTriangulated` and
`FlatModelGeneration` confirm the elementary kernel argument. The unit route and
all declared dependencies remain applicable, so no DAG edit is needed.

## Proved and sorry left

Closed 1 of 1 holes:
`CategoryTheory.weakSerre_bounded_homology_thick`
(node `lem-sfb-weak-serre-bounded-thick`).

Added 0 holes; split off 0 statements; 0 holes remain in the delivered module.
The local kernel calculation is fully proved. Single-file remote compilation
passed without errors or warnings. The axiom check reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

None. Both public imports support the statement and its structures. The private
import `Sheaf.Paper.CohomologyInWeakSerreSubcategory` is used explicitly. No nodes,
modules, unit steps, or source-library declarations are withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing boundedness API already gives
an interval and transfers it to a retract, so no separate finite-support proof
is needed. The sharper vanishing assertion is proved for arbitrary integers
`a` and `b`, including empty intervals. The kernel formula is independent of
membership, as expected; identity and zero retracts also satisfy the proof.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
