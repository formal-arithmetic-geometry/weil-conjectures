## What changed

Proved three theorems in `Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization`:
`enlargedComposition_projection_coherence`, `enlargedDirectInverse_coherence`, and
`enlargedLocalization_covering_families`. The first compares the two projections of each
pullback map explicitly, the second applies coefficient sheaves contravariantly and uses
Mathlib's adjoint composition and identity coherence, and the third constructs the inverse
localization functor from the original factorization and transports covering witnesses in
both directions. The covering proof uses `chartwise_etale_permanence` with explicit unused
index universes and includes empty covering families. No signatures or definitions changed.
The existing theorem node's proof text records these implementations.

## Proved and sorry left

Closed 3 of the original 7 holes, by declaration name:

- `AlgebraicGeometry.AlgebraicSpace.enlargedComposition_projection_coherence`.
- `AlgebraicGeometry.AlgebraicSpace.enlargedDirectInverse_coherence`.
- `AlgebraicGeometry.AlgebraicSpace.enlargedLocalization_covering_families`.

Added 0 holes and split off 0 statements. Four original holes remain, all owned by
`lem-trf-space-enlarged-ringed-composition-localization`:

- `AlgebraicGeometry.AlgebraicSpace.enlargedNormalizedRing_composition`.
- `AlgebraicGeometry.AlgebraicSpace.enlargedNormalizedRing_localization`.
- `AlgebraicGeometry.AlgebraicSpace.enlargedRingedMorphism_composition`.
- `AlgebraicGeometry.AlgebraicSpace.enlargedRingedMorphism_localization`.

These four theorem bodies and their source/proof docstrings are unchanged.

## No longer needed

Removed the unused private import
`Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation`. No written proof uses it;
the unfinished normalized-ring localization proof still needs that node as planned, so
its DAG dependency is retained. All public imports are preserved because they form the
existing public interface. No nodes or modules are withdrawn or claimed globally pruned.
No new modules or nodes were needed: Mathlib's pullback projection lemmas and
`Adjunction.leftAdjointCompIso_assoc`, `_comp_id`, `_id_comp` supply the categorical steps.
The mathematical proof dependencies are unchanged, including those of the four open holes.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The full-subcategory and over-category wrappers need
explicit projection equations rather than broad simplification of dependent pullback
objects. This is an implementation issue, not a statement repair or a route change.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
