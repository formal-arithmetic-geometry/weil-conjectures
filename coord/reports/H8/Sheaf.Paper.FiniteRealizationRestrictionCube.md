## What changed

Proved `realizationRestriction_directImage_cube`, retaining all existing public
signatures and definition bodies. Exact derived mates and equivalence triangles
identify the specified conjugated comparison with the localized ordinary
comparison. Four right-derived unit normalizations and the ordinary cube then
imply the desired derived cube. The generic normalized-cube calculation is
proved privately with independent derived-category Hom universes.

Three genuine steps are proved in new modules: the ordinary sectionwise cube,
the intrinsic realization/direct-image complex-unit normalization, and the
fixed-scalar complex-unit normalization. Profiling, local irreducibility,
and generic helpers were used before separating these calculations to meet the
per-file compile limit. All added imports in the assigned module are private
proof imports. The nodes describe the actual route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationRestriction_directImage_cube`
(node `lem-finite-realization-restriction-cube`). Zero holes added or split off.

The new theorems are also proved:
`AlgebraicGeometry.ProEtale.fixedScalarRestrictionDirectImage_unitQ_factors` and
`AlgebraicGeometry.Scheme.FiniteCompactScalar.realizationRestriction_ordinary_directImage_cube`.
No `sorry` remains in any delivered module.

## No longer needed

No original public import or original planned dependency is pruned. The
finite-open scalar-realization theorem is not used: the ordinary inverse mate
and the derived equivalence adjunction are computed directly by private helpers.
No source-library declaration, quarantined module, or parent dependency is
withdrawn. No postponed theorem is introduced.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid. The generic normalized-cube calculation in
`DerivedExactSquareCoherence` has a common derived-category Hom universe, whereas
the fixed-scalar and intrinsic categories here have different ones. Its argument
is generalized privately, preserving the shared interface. Restriction is never
assumed to preserve K-injectivity. Naturality along a K-injective resolution
extends each realization normalization to all complexes. Surjectivity of the
realization unit justifies the ordinary sectionwise calculation. The current
rework row was checked before copying the existing item; its source and Lean
attachment are preserved.

## New nodes

`lem-finite-realization-direct-image-unit-normalization` records the proved
all-complex normalization of the inverse intrinsic realization/direct-image
comparison.

`lem-finite-fixed-scalar-restriction-unit-normalization` records the proved
complex-level normalization of the inverse fixed-scalar comparison.

`lem-finite-realization-ordinary-restriction-cube` records the proved ordinary
sectionwise cube. Both nodes are strict parts of the argument and add zero holes.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
