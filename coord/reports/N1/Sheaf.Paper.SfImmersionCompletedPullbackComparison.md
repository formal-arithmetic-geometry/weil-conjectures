## What changed

Proved `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.finite_compatibility`.
The unit square uses Mathlib's inverse-mate unit identity. The transition square
uses `stratumReduction_evaluation`, the proved exact-tower evaluation interchange,
and naturality of strict tower transitions. The quotient cocycle follows by
transporting composition of strict derived-tower transitions through the finite
evaluation isomorphisms. The finite evaluation-transition equation is derived from
the public `pbc_reduction_adic_tower_laws` using the adjunction inverse identity.
Proved private helpers perform the diagram calculations over an arbitrary adic
datum, which is then specialized to the original integral datum.

The existing proved `ExactTowerAugmentedCounit.interchange_transition` is exposed
as public in its unclaimed owning module, without changing its statement or proof.
Both it and LevelwiseAdicTruncations have ordinary proof imports. The levelwise
module is unchanged. The owning nodes record the actual route and the public API.

The module object equality now evaluates an existing functor equality. A proved
generic equality-isomorphism identity shortens the ordinary transport proof.
`productComparison` keeps its published projection formula (reviewer fix); a generic
proved certificate identifies it with the canonical Roos product comparison,
including its equality transports, and `roosIso_exists` rewrites by it. `modulePull` has the same body and an explicit,
definitionally equal result type matching the tower statements. The Roos existence
proof rewrites by the certificate and applies its generic theorem directly.
These changes avoid repeated conversion through concrete limit and product data.
All theorem statements are unchanged. No target or shared Roos-model definition
is edited. The definition and API changes, consumers and meaning checks are in
`coord/changes/N1-immersion-finite-compatibility-api.md`.

The item compiled cleanly in 57.2 seconds. The API owner compiled in 31.1 seconds.
The unchanged consumers `IntegralImmersionPullbackNormalization`,
`IntegralStratumChartRestrictionsData`, and `SfCompletedPullbackMateFactorization`
all compiled against the delivered interfaces. No consumer adaptation was needed.

## Proved and sorry left

Closed one of the original four holes:
`AlgebraicGeometry.Scheme.ImmersionCompletedPullback.finite_compatibility`.
Added no holes and no split-off statements. The additional API-owning module
`Sheaf.CategoryTheory.ExactTowerAugmentedCounitEvaluation` has zero holes before
and after its visibility change.

The three original holes left, unchanged, all belong to node
`lem-sf-immersion-completed-pullback-comparison`:

- `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.completedProjection_compatibility`
- `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.rlimComparison_roos`
- `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.immersion_completed_pullback_comparison`

The proof uses existing stated dependencies, including the finite normalization
of the strict reduction pullback. Some imported dependencies still contain sorry.

## No longer needed

Removed the unused private `coefficientMap_eq`: `moduleObj_eq` now follows from
the existing full functor equality. No existing import, public declaration, module
or DAG dependency was removed. The existing coherence import stays a plain import
(reviewer fix). All new proof imports are used.
The other planned dependencies remain relevant to the three untouched holes.
No node or module was pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The existing normalized strict
tower comparison supplies the finite compatibility calculation; its representative
construction need not be repeated. The previous inferred pullback type and concrete
product-map presentation made repeated conversions expensive; the explicit type
and canonical comparison preserve the same data. The generic projection certificate
checks the latter change on every category, tower and evaluation equality proof.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
