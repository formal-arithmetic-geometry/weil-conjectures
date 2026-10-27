## What changed

Proved `AlgebraicGeometry.complementary_pure_subcurve_components` with its original signature and public imports unchanged. Four proved private topological helpers implement dimension-one component maximality, complementary component unions, and transport of components through an embedding. The proof retains the existing private import of `WeilConjectures.Topology.IrreducibleOpenComplementDimension` and uses the existing reduced-induced-subscheme uniqueness theorem for the final isomorphism. Updated the node's proof, proof dependencies, and proof origin to match the implementation.

The module compiles without errors or warnings in 6.3 seconds. A separate compile with `#print axioms AlgebraicGeometry.complementary_pure_subcurve_components` verifies the axiom set. The topological arguments require neither generic points nor reducedness; reducedness of Y is used in the final scheme isomorphism. Empty component sets and empty/full selections are handled uniformly by the same set identities.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.complementary_pure_subcurve_components` (node `lem-trf-complementary-pure-subcurve-components`). No holes remain in the item, no holes were added, and no statements were split off. All four private helpers are fully proved. The axiom check reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The proof no longer needs `lem-sc-scheme-sober`: Mathlib's `closure_sUnion_irreducibleComponents_sdiff_singleton` gives the closure argument in arbitrary spaces with finitely many components. Removed that node from this node's proof dependencies and steps; it remains available for other consumers. No import was removed, and no module was withdrawn. All other declared proof dependencies remain used. The existing approved dimension-drop tool remains used.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or assigned repair was found. The original generic-point arguments in steps 4 and 6 are valid but stronger than needed. The implemented argument uses the component's exclusive open part instead, preserving the original geometric route. No public definition, statement, or consumer interface changed.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
