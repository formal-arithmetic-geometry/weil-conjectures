## What changed

Proved both original theorems in `Sheaf.Paper.PointSystemNormalizedComparisonData`.
`exact_products` uses the sectionwise inverse-image equivalence, exact point sections,
sectionwise pro-etale products, and Mathlib exact products of modules.
The main theorem constructs the actual coefficient tower isomorphism, canonical additive
Roos comparisons, their signed coordinates, ordinary limit comparisons, natural derived
comparisons, arbitrary K-injective resolution formulas, and strict augmentations. The
realization isomorphisms descend through the ordinary derived localization.

The dependent `Data` bundle is represented by specialization of a generic `DataCore`;
its sixteen mathematical fields and equations are retained. Normalization and coefficient
predicates have names so structure declarations can share them. `systemRealization` uses
the same composite through the generic `systemModel`. The change record is
`coord/changes/point-system-comparison-generic-bundle.md`. No adopted source module changes.

## Proved and sorry left

Original holes closed (2 of 2):
- `WeilConjectures.PointSystemNormalizedComparison.exact_products`.
- `WeilConjectures.PointSystemNormalizedComparison.point_system_normalized_comparison_data`.

Holes left in the item: zero. Holes added: zero. Split-off statements: zero.
The proof uses existing declared dependencies, including dependencies with their own
existing holes; it does not claim those dependencies have been discharged here.
All private helpers have complete proofs.

## No longer needed

No original public import is removed: each is part of the existing statement interface.
The proof does not need the proposed `ExactProductFunctorRoosChainMaps` dependency
(`lem-cbc-exact-product-functor-roos-chain-maps`): the canonical comparison and its
augmentation formula are already supplied by `RoosComparisonHorizontalCoherence`.
The explicit signed matrix computation identifies its coordinates directly.
The proof does not directly need `lem-sf-exact-functor-derived-triangulated`:
localization descent and the existing exact-functor derived-category API suffice.
Their unrelated uses elsewhere are retained, and no module is withdrawn.

The proof uses only `natProducts` and `natProducts_preservesTowers` from
`ExactProductFunctorStrictLimit`, `ordinaryLimitIso` from `ExactProductFunctorRoosResolution`,
and `descendIso` from `ExactProductFunctorRoosDescent`. It does not assume the large
existential comparison bundles of those theorem modules to construct unspecified maps.

## Where the brief, the DAG or earlier work was wrong

The comparison construction requires the same fixed theta in both comparisons.
Choosing independently normalized existential comparison bundles would not immediately
supply that agreement. The proof constructs the product and Roos maps canonically first,
then descends them with the fixed normalized theta and eta. The representative equations
and unit equations give the resolution formulas for every K-injective resolution.

The full proof compiled as `Work109.lean` in 38.3 seconds, with no holes.
The polished source has also type-checked with no errors, though some server runs
exceeded 60 seconds; the delivery checks determine acceptance of the final file.
The concrete dependent bundle was expensive to elaborate and type-check. Its generic
representation and named property formulas preserve its content while avoiding repeated
construction of the entire coefficient-site expression. The unit route and node statement
are unchanged. No new mathematical node is introduced.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
