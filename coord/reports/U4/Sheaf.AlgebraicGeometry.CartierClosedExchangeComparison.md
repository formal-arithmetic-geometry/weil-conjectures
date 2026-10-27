## What changed

Filled `AlgebraicGeometry.ProEtale.geoCartier_closed_exchange_comparison` in
`Sheaf.AlgebraicGeometry.CartierClosedExchangeComparison` using the adjunction-mate
argument of its existing node and docstring. The theorem's signature and public import
are unchanged. Added one proof import, `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`.

The private proved helpers establish the comparison counit equation, composition and
commutative-square coherence, and normalization of the constant maps. The last calculation
transposes the two exchange composites and rewrites them to the same map. The constant-section
argument follows the existing proved calculations in `SupportQuotientPairPullback` and
`SupportSiteComparison`, reproduced locally to avoid their unrelated support and tensor
imports. Every private definition is an explicit construction through an adjunction or a record
of the existing functors and comparison isomorphisms. The diagram pasting and final mate
calculation are proved generically before specializing to the sheaf categories, avoiding
expensive reduction of the underlying Kan extensions during equality transport.

Expanded the existing node's proof into these four steps. No shared interface, target,
unit route, or other existing module changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.geoCartier_closed_exchange_comparison`
(node `lem-sfb-cartier-closed-exchange-comparison`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining in the item: 0.
No statements were split off. A clean server compile completed in 32.2 seconds.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The proof uses the existing comparison infrastructure,
whose own remaining obligations are unchanged.

## No longer needed

None of the item's original imports, nodes, or modules is pruned. All three declared
proof dependencies remain relevant. No extra support-cohomology or tensor modules are
imported for the constant-section calculation.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing mate-calculus plan works for the
stated arbitrary commutative square, without a pullback or closed-immersion assumption.
The proof retains arbitrary commutative coefficients, empty schemes, identity maps,
and the zero ring; no division, nonempty scheme, or finite-coefficient hypothesis is used.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
