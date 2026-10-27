## What changed

Proved `CategoryTheory.FiniteFilteredDerived.filteredFunctorGradedComparison` with
its original signature and every original definition unchanged. The construction
extends the canonical pure-object comparison along the natural span
`M → low(p+1) M ← high(p)(low(p+1) M)`. Naturality and cancellation along this span
reduce the transformation, identity and composition equations to pure objects.
Graded cones and joint detection of zero objects prove isomorphism detection.

Added two fully proved modules. `FilteredPresentationTruncationData` identifies the
explicit bounded-below source with `Complexes C`, compares their localizations and
graded functors, and transports the universal high/low functors and arrows.
`FilteredPresentationTruncation` proves finite graded support, joint detection of
zero objects, cutoff triangles, and the pure-span API used by the item.

The new public structures contain actual functors and natural arrows. Their
universal Hom bijections determine them up to the compatible isomorphisms used
here. No data is chosen from an undetermined existence assertion. Existing
signatures, public imports and non-theorem bodies were not changed. No consumer adaptation is required. A change record documents the static
visibility checker's classification of the new declaration-local helper scopes: 
`coord/changes/Y9-filtered-comparison-helper-scopes.md`. The two new nodes and the
item node now record the actual proof route. All three modules compile with
`lcompile.py --all`; the delivery command performs the remaining compiler and preflight checks.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.FiniteFilteredDerived.filteredFunctorGradedComparison`.

Also proved the new public theorems
`CategoryTheory.FiniteFilteredDerived.Presentation.truncationData`
(node `lem-trf-filtered-presentation-truncation-data`) and
`CategoryTheory.FiniteFilteredDerived.Presentation.truncationSpans`
(node `lem-trf-filtered-presentation-truncation`). All private helpers are proved.
Actual holes in the delivery: zero. Holes added: zero. Holes split off: zero.
The existing imported `CochainComplex.FiniteFiltered.filteredTruncationTriangle`
remains a dependency, as intended by the stage-3 brief.

## No longer needed

The item's direct proof import of
`Sheaf.Algebra.Homology.FilteredTruncationTriangle` is replaced by
`Sheaf.CategoryTheory.FilteredPresentationTruncation`; the former is still needed
transitively by `FilteredPresentationTruncationData`, so its module/node is not
pruned. The redundant direct import of `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
was removed (the API is already imported by the presentation). The Mathlib
zero-cone dependency is retained. No existing dependency
module or DAG node becomes unreachable through this delivery.

The proof does not use `FilteredTruncationData.unique_triangle`,
`high_hom_natural`, `low_hom_natural`, representative high/low comparisons,
`grade_truncation`, `grade_normalization`, or its pure-subcategory equivalence.
It uses the high/low support and Hom bijections and the graded comparisons and
exactness. The span construction avoids constructing functor-commutation
isomorphisms for the high/low truncation functors; normalization on pure objects
and naturality determine every coherence equation instead.

## Where the brief, the DAG or earlier work was wrong

The original plan referred directly to the concrete truncation theorem while the
item quantifies over arbitrary `Presentation`s. Their source categories express
strict bounded-below cochain complexes differently, and the grade functors must
be compared on morphisms, not just on objects. The new proved transport bridge
supplies these missing identifications by uniqueness of localization and full
faithfulness of `DerivedCategory.Plus.ι`.

No mathematical statement was weakened or disputed. The source's cutoff route
and the unit route are retained. Edge cases checked in the argument include the
zero complex, filtration grades outside either uniform bound, pure objects, and
empty support intervals. The lower-support and upper-support arguments use
finite bounds only to invoke the stated finite-interval preservation hypothesis.
No second agent was started, as required by the dispatcher brief.

## New nodes

`lem-trf-filtered-presentation-truncation-data` attaches the universal truncation
structure and its proved nonemptiness theorem. It transports the existing
concrete truncation calculus to any supplied presentation; it adds no hole.

`lem-trf-filtered-presentation-truncation` attaches the pure grade span structure
and its proved nonemptiness/joint-zero-detection theorem. Cutoff triangles are
recovered using the exact grades and universal quotient map, so no triangulated
structure on the localization equivalence is assumed. It adds no hole.

Change record: `coord/changes/Y9-filtered-comparison-helper-scopes.md`.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
