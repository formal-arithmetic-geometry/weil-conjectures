## What changed

Filled `AlgebraicGeometry.isAffine_of_qcqs_of_t1` in
`Sheaf.AlgebraicGeometry.QcqsZeroDimensionalAffine` using the three declarations
already named by the current DAG. The proof takes the finite Hausdorff affine
cover from `Scheme.exists_finite_hausdorff_affine_cover`, applies
`isClosed_and_isClosedImmersion_of_hausdorff_affine_cover` to each compact chart,
and applies `isAffine_of_finite_closed_cover` to the original chart inclusions.
The covering equation supplies an explicit preimage for every point. The argument
also permits `Fin 0`, so it retains the empty-scheme case without an extra hypothesis.
The two chart lemmas are imported privately; the closed-cover import is retained.

The existing node already records exactly this three-step argument, with the
correct proof dependencies and origin, so no node edit is needed. The approved
closed-cover tool is used at exactly its existing final step; the unit route stays.
LeanFinder, Loogle and grep searches found no direct replacement theorem.
The final single-file server compile passed in 1.6 seconds with no warnings.
Both added imports pass the project import-cycle check.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.isAffine_of_qcqs_of_t1`
(node `lem-sfb-qcqs-zero-dimensional-affine`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The proof uses the existing declarations
`AlgebraicGeometry.Scheme.exists_finite_hausdorff_affine_cover` and
`AlgebraicGeometry.isClosed_and_isClosedImmersion_of_hausdorff_affine_cover`,
whose own proofs currently contain sorry. Those existing dependency holes are
unchanged; this delivery completes the assigned assembly from their statements.

## No longer needed

Removed redundant direct proof imports:

- `Mathlib.RingTheory.Ideal.Maximal`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`

The first two are supplied by the interfaces of the imported chart lemmas. The
last two belong to the proofs of the chart lemmas and remain transitive
dependencies; their nodes are not globally pruned. All three current declared
proof dependencies are used. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing theorem docstring describes the older six-step expanded argument,
while the current DAG has already factored it into the two chart lemmas and the
finite closed-cover theorem. The proof follows that current DAG verbatim. There
is no mathematical discrepancy and no statement or definition change.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
