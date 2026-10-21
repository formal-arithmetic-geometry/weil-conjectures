## What changed

Proved the two assigned theorems from the stated projective-line decomposition,
Kummer and comparison results and two separately stated coherence lemmas. The
base-family construction now explicitly constructs the ordinary Chern family,
twisted comparison isomorphisms and untwisted decomposition arrows. The arbitrary
base class comparison and rational-point normalization are fully proved.

The diagonal proof constructs its supported Kummer boundary, transports the Ext
class through the invertible closed-source comparison, and applies the pre-trace
component formula. Its final calculation is the biproduct identity: the trace
kills the base component and sends the relative Chern component to one.

The unchanged generic `SpP1CartierCompatibility` is shared from the component
module, whose statement and parent both need it. The final witness uses a proved
generic existential constructor in the same assigned module.

The change record documents equivalent family, normalization and canonical-arrow
interfaces introduced to avoid repeated expensive derived-category type checking.
All three existing theorem signatures are unchanged. No adopted source module or
Challenge declaration changes, and no module is withdrawn. Single-file compiles
checked all seven modules during development. Generic semantic checks compiled
for the family constructor/projection inverses, five-clause normalization,
canonical existential-arrow elimination, Cartier realization, HEq trace wrapper,
and adjunction unit identity. The delivery tool reruns the packet checks.

## Proved and sorry left

Closed the two original holes:

- `exists_spP1BaseTraceConditions`.
- `spP1DiagonalIntegrals_of_twisted`.

Added two named holes, each in its own module with its source, complete proof in
words and DAG node:

- `spP1BaseChange_of_normalized`: arbitrary-base naturality of the normalized
  splitting and its trace.
- `geoP1_diagonal_comparison_components`: comparison of the ordinary supported
  diagonal component formula with the canonical pro-etale arrows, before trace.

This is a decomposition, with two holes closed and two added (net zero), not a
claim that the targets are axiom-free. The assigned module has zero remaining
holes; the seven-module packet has two. The new declarations
`ordinaryFiniteClass_bijective_arbitraryBase`,
`exists_spP1NormalizedDecompositions`, and
`spP1RationalPointChern_of_normalized` are fully proved and introduce no holes.

## No longer needed

Removed these original private imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`.
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek`.

The proof uses the specific existing comparison, splitting, Kummer and closed
immersion APIs instead of assembling the entire six-functor infrastructure anew.
For this item's proof, the global GeoCartierClass family existence theorem is
unnecessary: the needed class is transported directly through the invertible
source comparison. The global GeoP1Cohomology family theorem is also unnecessary:
the normalized family is constructed from ordinary splittings. Neither upstream
declaration is removed; their own dependencies and the unit routes remain.
No existing module or unit statement is pruned or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing class-comparison API imposed quasi-compact hypotheses, whereas the
assigned normalized decomposition ranges over arbitrary bases. The new
arbitrary-base class comparison proves the required extension using the existing
injective-forgetful acyclicity result. The Noetherian descent argument then
identifies the canonical ordinary Chern class with the splitting class.

The originally nested function and proposition representations caused repeated
expansion of large derived Hom types and exceeded the single-file time limit.
The equivalent structures and named canonical maps retain the exact values and
all conditions; the change record describes their constructor/projection and
canonical-substitution checks. The source diagonal is the hom of a component of the inverse composite natural
isomorphism. The kernel stores that constructed isomorphism and the literal
Cartier and chart arrows with their types. Its typed realization requires HEq to
these values. This preserves invertibility and fixes every representative
uniquely, while avoiding repeated Hom-type normalization in data assembly. The
Cartier and chart expressions retain their inferred types; the realization's HEq
conditions require exactly the original prescribed typed arrows.

## New nodes

- `lem-sp-ordinary-finite-class-arbitrary-base`: arbitrary-base ordinary class
  comparison; proved.
- `lem-sp-p1-normalized-family-core`: canonical normalized family; proved.
- `lem-sp-p1-rational-point-chern`: rational point versus O(1) Chern class; proved.
- `lem-sp-p1-base-change-normalized`: normalized family exchange; one named hole.
- `lem-sp-p1-diagonal-comparison-components`: pre-trace diagonal comparison;
  one named hole.

The two original theorem nodes now record these actual proof routes. Existing
interface nodes list the additional declarations. No DAG node is deleted.

Change record: `coord/changes/P4-projective-line-canonical-component-api.md`.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
