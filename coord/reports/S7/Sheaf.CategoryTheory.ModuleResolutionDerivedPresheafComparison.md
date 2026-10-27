## What changed

Completed all six theorem bodies in
`Sheaf.CategoryTheory.ModuleResolutionDerivedPresheafComparison`, retaining every
public declaration, signature, definition and public import.

`exists_resolution` uses the canonical injective resolution extended to integer
degrees. Acyclicity after forgetting scalars follows objectwise from
`injective_module_abelian_acyclic`, the existing natural comparison of object
cohomology with derived sections, and exact evaluation of presheaves.
The main comparison then uses the existing acyclic-unit theorem directly.

Proved private helpers construct strict lifts using Mathlib's bounded-below
injective model structure, invoke the existing homotopy-uniqueness theorem,
identify `qIso.hom` with actual localization, and calculate naturality of the
specified comparison. The abelian-resolution and module-map assertions use those
helpers. The identity assertion specializes module-map naturality and applies
acyclic quasi-isomorphism preservation.

For degree-zero normalization, the incoming differential is zero, so left
exactness preserves the degree-zero homology map. The two isomorphisms are
constructed from the prescribed augmentation maps; their compatibility follows
from the strict comparison equation. No arbitrary identifications are chosen.

Updated the existing node's proof, proof dependencies and proof origin to record
the direct acyclic-unit route and the existing derived-sections comparison.
Added only private proof imports for `PlusHomology`, `RightDerived.Comp`, and
`CohomologyRightDerivedSections`. Suppressed the unused-section-variable linter
locally on `exists_resolution` to preserve its original public signature.

## Proved and sorry left

Closed all six original holes, in namespace
`CategoryTheory.ModuleResolutionDerivedPresheaf`:

- `exists_resolution`
- `module_resolution_derived_presheaf_comparison`
- `abelian_resolution_comparison`
- `module_map_comparison`
- `identity_comparison`
- `degreeZero_normalization`

All are attached to existing node
`lem-sfb-module-resolution-derived-presheaf-comparison`.
No `sorry` remains in this module. No holes were added or split off, and all
private helpers are proved. This is a proof delivery, not a decomposition.

## No longer needed

Removed the following private imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: no unbounded
  K-injective construction is used. The Grothendieck-abelian instance already
  comes from the existing public source-library import.
- `Mathlib.CategoryTheory.Abelian.Injective.Resolution`: its resolution API is
  available through the retained imports.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: exactness
  instances already come from the retained public module-sheaf imports.
- `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`: evaluation's exactness
  API is available through the retained imports.

No declared mathematical proof dependency was dropped: all the existing nodes
still contribute the constructions, exactness, objectwise computation, strict
lifts, homotopy uniqueness or acyclic quasi-isomorphism theorem. None of their
modules is withdrawn. The unbounded-resolution and generator clauses of
`prop-pur-kinjective-resolutions-exist` are unused; its Grothendieck-abelian clause
is still needed.

## Where the brief, the DAG or earlier work was wrong

The original plan needlessly constructed an abelian injective resolution to
prove invertibility of the main comparison. The existing proved theorem
`Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic` gives it directly.
Its existing node `src-right-derived-functor-plus-acyclic-unit` is reused as a
generic categorical tool; it does not bypass the unit's route.

The existing node `lem-sc-site-cohomology-right-derived-sections` supplies the
precise Ext/object-cohomology comparison needed by the objectwise acyclicity
argument. Both imported results were read against the current source. No new
nodes or declaration repairs were needed.

The required initial delivery check pushed nothing: it rejected the retained
one-hole proof because of an unused-section-variable warning. That warning is
handled without changing its signature; the other five proofs have also been
completed. Edge cases introduce no extra hypotheses: zero modules and rings,
empty sites, and arbitrary choices of zero objects in negative degrees are all
covered by the categorical constructions and `IsZero` arguments.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
