## What changed

Proved all seven original holes in `Sheaf.Algebra.Homology.FiniteFilteredLocalization`.
Constructed the binary direct-sum filtration and the zero filtered object explicitly.
Proved that binary sums preserve finite bounds and injective graded objects, using
additivity of grading and the biproduct identity to extend morphisms componentwise.
The terminal and binary product universal properties give finite products.

Proved graded identity, composition and additivity by uniqueness of restrictions through
monic inclusions and of graded maps through epimorphic cokernel projections.
The graded-acyclic homotopy objects form a triangulated subcategory, whose `trW` class
is exactly the graded quasi-isomorphisms. Mathlib then supplies fractions and
triangulation compatibility.

Added the proof-only import `Sheaf.Paper.FiniteFilteredGradedExactness`. Its existing
theorem proves that forgetting a graded-acyclic complex is acyclic, degree by degree.
The cone criterion and ordinary localization prove `filteredEvaluation_inverts`.
Moved the finite-product declarations after the additive graded functor, to use the
functor in the injective-grade proof. All public signatures and definition bodies stay
unchanged. The DAG proof and dependencies now record the implemented argument.

Validation: the complete module compiles on the project server without warnings in
12.5 seconds. Edge cases covered by the construction include the empty product, the
zero category, a reversed fixed interval, a single grade, and bounds varying by degree.

## Proved and sorry left

Closed seven of seven original holes, by declaration name:

- `CategoryTheory.finiteFiltered_hasFiniteProducts`
- `CategoryTheory.filteredGraded_map_id`
- `CategoryTheory.filteredGraded_map_comp`
- `CategoryTheory.filteredEvaluation_additive`
- `CategoryTheory.finiteFilteredQuasiIso_leftFractions`
- `CategoryTheory.finiteFilteredQuasiIso_triangulation`
- `CategoryTheory.filteredEvaluation_inverts`

Zero holes remain in the item; zero holes were added; zero were split off.
The final inversion proof uses the already stated
`CategoryTheory.FilteredObject.finite_filtered_graded_exactness`
(node `lem-trf-finite-filtered-graded-exactness`), whose proof remains a separate item.

## No longer needed

No original imports or dependency nodes were removed. The original public imports
retain the module's statement interface, including the node's subquotient dependency.
The proof needs neither a separate spectral-sequence convergence theorem nor a
filtered-injective resolution or comparison theorem: those modules were not imported.
No pre-existing dependency of this node was pruned (the old proof_deps was empty).

## Where the brief, the DAG or earlier work was wrong

The existing node had no numbered proof steps despite the seven postponed validity
proofs. Its proof field is now filled with the actual additive, product and
Verdier-subcategory argument. No statement or definition repair was necessary.

The first dry run rejected a temporary file-scope `open ZeroObject` change. The final
file uses only declaration-local opens. A compile timeout in the first product attempt
was traced to instance search unfolding constructed graded objects; explicit types
for the two injective instances fixed it without raising any limit.

Change record: `coord/changes/finite-filtered-localization-proof-order.md` records the
reordering of existing declarations and instance attributes and the private helper
instances for the independent reader. No downstream adaptation is needed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
