## What changed

Proved `freeScalarMap_isIso` by identifying the specified transpose with the
K-flat computation counit, the single-complex comparison and the ordinary
free scalar isomorphism. The latter is obtained by uniqueness of left adjoints.
Added a proof import of `Sheaf.Paper.FreeParameterDegreeZeroData` and proved
private compatibility helpers. Cached local tensor instances prevent repeated
expansion of the sheaf monoidal structures. Existing public signatures,
definitions and imports are unchanged.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.ProEtale.FreeParameterEvaluation.freeScalarMap_isIso`.

The original hole
`AlgebraicGeometry.ProEtale.FreeParameterEvaluation.scalarPullComparison_isIso`
remains, attached to `def-sfb-free-parameter-scalar-maps`. No holes were added
and no statements were split off. All private helpers are proved.

## No longer needed

None of the existing public imports, nodes or modules is removed.
The completed free-map proof needs only the recorded degree-zero flatness and
the existing ordinary and derived scalar adjunctions. The attempted normalized
geometric-comparison imports are not part of this delivery because the second
original theorem is left untouched.

## Where the brief, the DAG or earlier work was wrong

The owning definition node had empty proof and proof_deps despite containing
two invertibility assertions. Its proof now records the free-map argument and
the original K-flat geometric-comparison argument for the remaining theorem.
The free-map proof does not assume the coefficient map is flat or the free
module is projective. The main formal difficulty was compatibility of the
single functors, homotopy quotient and derived adjunction unit; backward
definitional equalities and local instance caches are used for those checks.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
