## What changed

Proved `AlgebraicGeometry.Scheme.Hom.finite_field_degree_isomorphism_transport`
with its full original signature and all six clauses. The canonical ring equivalence
comes from `asIso u.hom.appTop`; global-sections naturality proves the scalar square.
A proved private helper `transport_basis` constructs a basis via finitely supported
coordinates along a semilinear equivalence. Applying it forward and backward proves
the basis iff. Mathlib cancellation of isomorphisms proves finiteness invariance,
and `Algebra.finrank_eq_of_equiv_equiv` proves the degree equality directly.
The node's proof, proof dependencies, and proof origin now describe this proof.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.Hom.finite_field_degree_isomorphism_transport`
(node `lem-weil-pbc-finite-field-degree-isomorphism-transport`).
No holes remain, no holes were added, and no results were split off.
The private basis helper is also fully proved. Single-file compilation succeeded;
the delivery checks compile the final file and probe declaration axioms.

## No longer needed

Removed the four unused proof imports:
`Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.Morphisms.Affine`,
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace`, and
`Mathlib.RingTheory.Finiteness.Defs`.
Their elementary interfaces are already available through the retained public imports.

The proof no longer needs
`lem-weil-pbc-finite-over-field-affine-finite-dim`: the Mathlib dimension comparison
works without finite-dimensionality. No module or public declaration is withdrawn.
The finite-composition node remains as the ingredient supplying multiplicativity
and hence the finite-morphism cancellation API. The unit's own realized statements
and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned finite-dimensionality and finite-basis
extraction in step 5 are unnecessary. Coordinate equivalences also express the
finite-sum basis argument for every index universe without auxiliary results.
Checked empty and infinite index types, zero section rings, and nonfinite structure
maps: none requires an additional hypothesis.

Searches used the prescribed Loogle query for
`Algebra.finrank_eq_of_equiv_equiv`, LeanFinder for semilinear basis transport,
and ripgrep over Mathlib and both library roots. The relevant Mathlib definitions
and the upstream `finrankΓ_eq_of_iso` proof were read; the latter covers only the
degree clause, so the full theorem still requires the proof delivered here.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
