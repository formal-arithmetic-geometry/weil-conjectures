## What changed

Filled all four theorem proofs in `lean/Sheaf/Paper/ConstructibleExtContinuity.lean` without changing any statement or definition. The main comparison uses the existing stratum theorem and finite-extension devissage, then transports from the canonical colimit to the supplied cocone. Bounded generation follows by induction on the existing finite-cone witness, using rotation and addition of extension lengths. The sheaf corollary applies this result to degree-zero complexes. The integral clause enlarges the allowed shift set by monotonicity.

Added proof-only imports of ConstructibleHomContinuityDevissage, ModuleObjects.MapMod, ConcreteCategory.EpiMono and DerivedCategory.FullyFaithful. Existing CoefficientHeartGeneration and ConstructibleExtContinuityStratum imports are retained and used. Private proved helpers transport finite constant models across isomorphisms and construct models for zero. Updated the existing node's proof route and dependencies; no public interface changed.

## Proved and sorry left

Closed four original holes, all under node `sk-lem-constructible-ext-continuity`:
- `AlgebraicGeometry.ProEtale.constructible_ext_continuity`.
- `AlgebraicGeometry.ProEtale.bounded_constructible_ext_generated`.
- `AlgebraicGeometry.ProEtale.constructible_sheaf_ext_continuity`.
- `AlgebraicGeometry.ProEtale.integral_finite_extension_ext_generated`.

No holes remain in the delivered module: four closed, zero added, zero split off. No nodes were added. The retained module compiles cleanly against the current compiled library (6.8 seconds); the declaration comparison confirms no existing signature, definition body or public import changed. All lines meet the 100-character limit. Imported dependencies may still contain their existing named holes; this delivery proves the four theorems from those declared dependencies.

## No longer needed

Removed proof imports Mathlib.CategoryTheory.Triangulated.Pretriangulated, Mathlib.Algebra.Category.Grp.AB, Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four, Mathlib.AlgebraicGeometry.Morphisms.Immersion and Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle and Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale. Public imports are preserved.

The node no longer directly uses lem-weil-pbc-hom-out-of-triangle-exact, lem-weil-pbc-filtered-colimit-abelian-groups-exact or lem-weil-pbc-five-lemma: the existing devissage module packages precisely that argument. These remain indirect dependencies of devissage; no global pruning of those modules is claimed. The direct dependencies lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-noetherian-open-subscheme-noetherian and lem-pqf-qc-immersion-open-closed-factor are replaced by Mathlib's Noetherian-space instances and the actual factorizations already carried by generators. The direct dependency lem-sf-derived-ses-triangle is unnecessary because the integral hypothesis already supplies an extensionProductIter witness. No unit step is bypassed: devissage and stratum continuity are both used.

## Where the brief, the DAG or earlier work was wrong

The retained report said CoefficientHeartGeneration was absent. It is now present in current sources and its coefficientHeart_generation theorem is used. No mathematical statement repair was needed. Quasi-compactness of open immersions follows from the Noetherian structures transported along embeddings; no additional hypotheses are imposed. Empty schemes, rank zero and zero complexes are covered by the same constructions. All integer shifts are handled by shiftClosure, and cone steps are rotated with their existing distinguished-triangle signs.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
