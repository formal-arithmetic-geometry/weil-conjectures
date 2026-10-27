## What changed

Partial proof delivery for `Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent`.
Proved `resolution_formula` without changing any existing
statement or definition. The existing comparison definitions precede their first proof use.
Private helpers identify the chain comparison with the derived unit and record its
naturality. The common cochain-unit normalization is split into the new module
`Sheaf.AlgebraicGeometry.RingedExchangeChainUnit`, with its source, proof in words and
DAG node. It is a genuine preliminary step: the item proves the resolution formula
by cancellation and naturality. The item publicly imports the lower module,
which now carries the nine shared definitions
verbatim. All existing names and bodies are unchanged.
Locally irreducible operations bound unfolding only during the new calculations;
transparency is restored before the previously proved declarations.

## Proved and sorry left

Closed 1 of the 10 incoming holes; added 1 hole; split off 1 statement.
This is a decomposition with no net hole closed:

- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.resolution_formula`

Nine original holes remain, all in the same namespace and attached to
`lem-sf-ringed-restriction-exchange-open-descent`:

- `actualCoefficients_coherent`
- `degreeZero_normalization`
- `open_comparison`
- `open_sectionwise`
- `openCube_exists`
- `open_restriction`
- `open_descent`
- `identityCoefficients_coherent`
- `identity_normalization`

One new hole remains:

- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.exchange_chainUnit`, in
  `Sheaf.AlgebraicGeometry.RingedExchangeChainUnit`, node `lem-sf-ringed-exchange-chain-unit`.

The original coefficient-coherence proof fields remain unproved; the new argument works
for every supplied coherent square. The degree-zero formula remains unproved.

## No longer needed

No imports are removed and no whole modules are withdrawn. The resolution-independence
argument no longer needs `lem-sp-kinjective-comparison-principle` or its module
`Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple`: the formula holds for all resolution
choices and computes the same fixed derived mate. This dependency is removed from step 4,
from the node's proof dependencies and from its top-level `tool_uses` list.
Other consumers of that lemma are unaffected.
The still-unproved declarations retain their other source proof dependencies and route.

## Where the brief, the DAG or earlier work was wrong

The planned separate construction of comparisons between pairs of resolutions is unnecessary.
The library already proves the needed unbounded cochain mate calculation in
`Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare`, and identifies the actual ambient
square with the localized ordinary square in
`Sheaf.AlgebraicGeometry.ProEtaleRingedSquareLocalization`. Using those results first gives
a normalization on every complex; naturality and the K-injective comparison isomorphisms
then prove the two-resolution formula directly. The degree-zero equation remains a
separate, unproved step.

## New nodes

`lem-sf-ringed-exchange-chain-unit` records compatibility of the specified derived mate
with the canonical cochain units. It is the common preliminary step before the resolution
formula. Its proof plan specializes the existing generic cochain mate
calculation using the proved ambient-square localization theorem, and cancels the lower
factorization isomorphism. Edge cases: zero complexes, empty schemes and identity maps
use the same naturality calculation without additional assumptions. The module move is
recorded in
`coord/changes/ringed-exchange-chain-unit-operations.md`; every moved declaration is verbatim.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
