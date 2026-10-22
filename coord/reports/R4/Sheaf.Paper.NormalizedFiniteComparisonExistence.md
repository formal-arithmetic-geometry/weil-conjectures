## What changed

Proved AlgebraicGeometry.Scheme.cbcNormalizedFiniteComparison_exists in
Sheaf.Paper.NormalizedFiniteComparisonExistence, preserving its signature and both
representative-normalization predicates. All added declarations are proved private helpers.

The existing canonical completed coefficient map is an isomorphism. Scalar extension
along it is an equivalence by uniqueness of left adjoints, so completed module pullback
is exact, as is its strict tower functor. Its actual universal derived counit is therefore
invertible on every complex. This avoids the planned intermediate flatness argument.

Compose the actual reduction, exact open-extension, tower-pullback and evaluation
counits, and then the unchanged ordinary coordinate isomorphisms cbcSourceLevel and
cbcTargetLevel. Compare these with the existing finite model maps. On K-flat complexes
all these maps are invertible. A private general localization argument descends their
quotient to the required natural isomorphism. Its factorization equation is exactly
the original normalization, including every original counit.

The generic comparison API states its conclusion using the original nested source
and finite-model formulas. This avoids expensive concrete conversion between the
complex functor of a composite and the composite of complex functors. Local
irreducibility protects the coefficient limit and chosen derived functors and counits.
Proof checking is synchronous; all kernel and linter checks remain enabled.
The full module passed lcompile.py in 58.1 seconds. No compile limit is changed.

Added only private proof imports. Updated the item's existing DAG proof, proof_deps
and proof_origin to this route. No existing definitions, public imports, statements, consumer
modules, source-library declarations or target signatures change.

Preflight classified the added local attribute commands as an interface-context edit.
Added coord/changes/R4-normalized-finite-comparison-proof-context.md, recording all
local attributes, the unchanged theorem signature, and all three transitive consumers.
Only CompletedRingStrictFiniteExchange uses the theorem directly; it is held by M3.
No consumer adaptation is needed because the public interface is unchanged.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.Scheme.cbcNormalizedFiniteComparison_exists
(lem-cbc-normalized-finite-comparison-existence).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. No split-off statements.
The proof uses existing declarations with their existing proof obligations, as intended
by stage 3; it does not claim to have closed all transitive library obligations.

## No longer needed

The proof does not use these originally planned direct dependencies:

- lem-cbc-ringed-open-strict-reduction / Sheaf.Paper.RingedOpenStrictReduction:
  the two actual ordinary coordinate isomorphisms are descended directly.
- lem-cbc-ringed-open-flat-resolution / Sheaf.Algebra.Homology.RingedOpenFlatResolution:
  exact completed pullback makes its counit invertible on every tower complex.
- lemma-weil-pbc-completed-pullback-reduction / Sheaf.Paper.CompletedPullbackReduction:
  direct localization of the ordinary comparisons gives exactly the fixed finite models.
- lem-pur-left-derived-from-kflat-class /
  WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass:
  the needed derived functors already exist; only their comparison is descended, using
  the resolving-full-subcategory localization argument already proved in
  SiteDerivedTensorDescentIndependentCoefficients.

These nodes are removed from this item's proof_deps; none of their modules is withdrawn,
because other library proofs still use them. No existing import line is removed from
the item. The original public model import remains necessary.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan asks for more intermediate results
than this existence assertion needs. The implemented proof uses exactness of completed
coefficient pullback and retains the specified ordinary finite coordinate maps, rather
than introducing new finite-evaluation comparisons.

The general descent helper proves its localization factorization equation in Lean;
there is no additional assumption that a natural transformation descends. The final
normalization equations follow by expanding the original model definitions and
functor map-composition equations. Empty opens, empty schemes, the zero complex and
the zero coefficient ring introduce no extra hypotheses. The argument remains unbounded
and makes no completeness or quasi-compactness assumption.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
