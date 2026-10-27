## What changed

Proved `AlgebraicGeometry.topologicalKrullDimAt_eq_max_component_dimension` in
`Sheaf.AlgebraicGeometry.LocallyAlgebraicDimensionComponents`, keeping its public signature
and public imports unchanged. Added two proved private topological helpers: local dimension
is monotone under an inducing map and invariant under a homeomorphism. Added the private
proof import `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType` for the
finite-type algebra structure on affine sections.

For each component C through x, its reduced induced closed subscheme Y is irreducible and
locally of finite type over k. The existing irreducible dimension theorem identifies dim C
with dim_y Y, which is bounded by dim_x X using the inducing helper. For attainment, use
the existing affine component formula on an affine neighbourhood of x, map its attaining
component D into X, and extend that irreducible image to a global component C. The induced
embedding D→C and the first bound force equality. All component choices occur inside the
theorem proof; there is no new data definition or choice from an unproved existence result.

Updated the theorem proof docstring and the item's node proof, proof dependencies and
proof origin to this argument.
The unit route is preserved: this node is not a realized unit statement or proof step.
The empty case is vacuous because x is an input. The argument also applies at a generic
point, to reducible or nonreduced schemes, and without quasi-compactness or separatedness.

Validation: the final module compiled through `lcompile.py` in 2.8 seconds, exit code 0,
with no warnings. All Lean lines are at most 100 characters. Only the permitted node
fields `proof`, `proof_deps` and `proof_origin` changed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.topologicalKrullDimAt_eq_max_component_dimension`
(node `lem-trf-locally-algebraic-dimension-components`).

Zero holes remain in the item. Zero holes added; zero statements split off.
The private helpers `dimensionAt_le_of_isInducing` and `dimensionAt_homeomorph` are proved.
Both mathematical inputs, `AlgebraicGeometry.dimension_locally_algebraic` and
`AlgebraicGeometry.dimension_at_point_components`, already have complete theorem bodies
in the adopted source library. No source-library files were changed.

## No longer needed

Removed the private import `Mathlib.Topology.Sets.Closeds` and the proof dependency
`lem-weil-pbc-open-subspace-irreducible-closed-correspondence`. Neither the order isomorphism
of irreducible closed subsets nor the component restriction bijection is needed: extending
the attaining affine irreducible subset and comparing the two dimension bounds suffices.
The topological closed-set types remain available through the imports needed for the
closed subscheme construction. This is removal of a proof dependency and direct import,
not withdrawal of Mathlib's module or of any library declaration.

All other original proof dependencies are retained and used. The new route also records
the existing Mathlib dimension-monotonicity leaf and the local-dimension definition.
No modules or declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statements or interface defects found. The original plan is valid but its
component correspondence and equality of the dimensions of C and C∩U can be avoided.
The proof uses local dimension on the closed subscheme instead, then uses an affine
attaining component only for the opposite inequality.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
