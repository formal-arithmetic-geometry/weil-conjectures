## What changed

Filled the proof of
`AlgebraicGeometry.Proj.isBasis_positiveDegree_basicOpen_and_isAffineOpen`
in `lean/Sheaf/AlgebraicGeometry/ProjStandardOpenBasis.lean`.
The basis conjunct is `(Proj.standardOpenProperties.{u, v, 0} 𝒮).1`, from the existing
private proof import `WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`.
The affine conjunct applies Mathlib's `Proj.isAffineOpen_basicOpen` with the
homogeneity and positive-degree hypotheses in its required order.
The existing statement, imports, and DAG proof plan are unchanged.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Proj.isBasis_positiveDegree_basicOpen_and_isAffineOpen`
(node `lem-sc-proj-standard-open-basis`).
Zero holes remain in the item, and zero holes were added or split off.
The proof uses the already proved library basis theorem and Mathlib affine-chart theorem.

## No longer needed

None. Both existing imports are used. Both planned proof dependencies are retained:
`lem-weil-pbc-proj-standard-open-inclusion` supplies the basis clause, and
`def-nagata-affine-proj` supplies the affine-chart identification, through Mathlib's
proved `Proj.isAffineOpen_basicOpen`. No nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The two steps of the existing DAG proof are implemented directly.
The unit statement and its route are preserved. No new hypotheses, statement repairs,
consumer adaptations, or new nodes are needed. The existing results apply also to empty
Proj and to zero or nilpotent homogeneous elements; no nonzero hypothesis was introduced.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
