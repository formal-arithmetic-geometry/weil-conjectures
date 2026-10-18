## What changed

Proved `CategoryTheory.orthogonalTriangle_counit_normalization` in
`Sheaf.CategoryTheory.OrthogonalTriangleCounitNormalization`, preserving its statement and
public imports. Hom exactness gives surjectivity; the inverse-rotated triangle and shifted
orthogonality give injectivity. Full faithfulness and adjunction naturality give bijective
postcomposition with the transpose. An explicit two-sided inverse makes it invertible;
`Triangle.isoMk` constructs the requested triangle isomorphism and transports distinguishedness.
The node's first proof step now records the inverse-rotation implementation.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.orthogonalTriangle_counit_normalization`
(node `lem-sfb-orthogonal-triangle-counit-normalization`). Added 0 holes; split off 0.
No `sorry` remains in the delivery.

## No longer needed

None. Both original public imports are required by the statement. All three declared proof
dependencies are used through their recorded Mathlib declarations:
`lem-weil-pbc-hom-into-triangle-exact`, `def-weil-triangulated-category`, and
`lem-weil-pbc-adjunction-of-natural-bijection`. No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The shifted injectivity argument can be written more directly
using exactness on the inverse rotation, which already has `B[-1]` as its first vertex.
No definitions, signatures, consumer modules, or unit routes changed.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
