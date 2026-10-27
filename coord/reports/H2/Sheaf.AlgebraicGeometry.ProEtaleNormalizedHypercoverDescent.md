## What changed

Filled the proof bodies in `Sheaf.AlgebraicGeometry.ProEtaleNormalizedHypercoverDescent`
while retaining every existing public statement. Reused exact module evaluation,
the published hypercover total comparison, and injective augmented rows. The remaining
argument constructs the signed coproduct-total homotopy, transports the actual derived
unit to complexes, compares injective resolutions, and proves normalization and
coefficient/refinement compatibility by cancellation. Private helpers expose the
forgetful functor's homology preservation and covering-induced represented epimorphisms.

The degree-zero identification is proved directly: the coefficient-single complex
has zero summands off degree zero, so its total coproduct inclusion is invertible;
chain-map compatibility follows from the signed total differential. This avoids
importing the larger bicomplex-columns development. Generic private lemmas handle
composition of exact functors and the derived unit's resolution computation. Narrowly
scoped transparency settings and sequential elaboration avoid repeated unfolding of
concrete module and derived functors. The module has no private aliases for abelian
structures. Two public proved lemmas cache the existing sheafification and local
bijection instances. Original public imports stay unchanged.

Row restriction is now explicitly the map of `rowRestrictionFunctor`, formed from
right-op, precomposition, the existing section presheaf functor, alternating cofaces
and extension by zero. Its object and component maps are definitionally the published
section rows and row restrictions. `rowRefinementNat` uses this functor's map, so
identity, composition and naturality use the functor laws directly. The change record
is `coord/changes/proetale-normalized-row-functor.md`. There are no current Lean
importers; DAG parents are retained. No upstream source file is changed.

The node now records the existing total-comparison and injective-row interfaces actually
used by the proof. No existing public imports, signatures or target statements were changed.

## Proved and sorry left

Original hole count: 17. The completed proofs close all 17 original holes:
`evaluation_additive`, `evaluation_exact`, `evaluation_quasiIso`, `total_quasiIso`,
`augmentation_quasiIso`, `coefficient_resolutions`, `descent`, `comparison_formula`,
`comparison_naturality`, `signed_homotopy`, `resolution_comparison`,
`comparison_normalization`, `rowRefinement_naturality`, `refinement_squares`,
`comparison_refinement`, `refinement_functoriality`, and `single_sheaf`.
All names are in `AlgebraicGeometry.Scheme.ProEt.NormalizedDescent`.

There are zero `sorry` tokens in the submitted module and zero holes added or split off.
The refactored module compiled in 55.6 seconds; the combined delivery compile and
axiom probe passed in 56.6 seconds before redundant instance binders were removed.
The final version retains the original section parameters and suppresses
unused-section-instance diagnostics while retaining the original theorem signatures.
The delivery preflight checks the final refactored packet.

## No longer needed

Removed proof imports `Sheaf.Algebra.Homology.BoundedBelowTotalComparison`,
`Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentation`, and
`Sheaf.CategoryTheory.KInjectiveComputes`. The initially considered proof imports
`WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns` and
`Mathlib.Algebra.Homology.TotalComplexSymmetry` are also unnecessary after the
direct degree-zero coproduct proof.

The node does not directly need `lem-weil-pbc-bounded-below-total-column-comparison`:
`lem-weil-pbc-proetale-hypercover-total-quasi-iso` already states and proves its application
for the published total. The generic comparison remains an indirect dependency of that
reused theorem and is not globally withdrawn.

The node does not directly need `lem-weil-pbc-ringed-hypercover-injective-augmentation`:
`lem-weil-pbc-proetale-hypercover-injective-row` packages the required application.
The generic augmentation remains an indirect dependency of the reused row theorem.

`lem-weil-pbc-site-sheaf-sets-epi-locally-surjective` is unnecessary for the matching-arrow
step: the epimorphism follows directly by sheaf separation on the covering sieve.
`lem-sp-kinjective-computes` is unnecessary: Mathlib's
`CochainComplex.isKInjective_of_injective` gives precisely the needed K-injectivity.
The obsolete corresponding top-level `tool_uses` entries were removed, preserving the
order of all remaining entries. No module or upstream declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics is unchanged. Two previously proved interfaces already package
the total-comparison and injective-row applications, so duplicating those constructions
would be unnecessary. Evaluation exactness and forgetting scalars require explicit
universe choices to avoid ambiguous colimit instances. The comparison uses the canonical
right-derived unit, rather than choosing unspecified derived computation isomorphisms.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
