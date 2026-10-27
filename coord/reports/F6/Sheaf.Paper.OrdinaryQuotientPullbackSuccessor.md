## What changed

Proved `WeilConjectures.ordinaryQuotientPullback_successor` with its existing signature. The
proof conjugates the source successor by the given level isomorphisms and compares maps on
finite pullback generators of tensor units. The ordinary adjunction unit followed by the
inverse-limit projections supplies compatible sequence sections; `M.unit_tensor` identifies
their finite evaluations with those tensor units. Naturality of the sequence pullback unit then
gives compatibility before applying the level isomorphisms. The published pullback-transition
and tensor-transition characterizations identify the other side on the same generators. Finite
linearization, the pullback adjunction and the normalized scalar-reduction adjunction prove
equality on all sections.

All added helpers are private and proved in the item module. The proof import exposes existing
private construction APIs from `IntegralOperationsWellDefined` and the proved scalar-unit
normalization from `CoherentQuotientOrdinaryLift`. The latter has no holes and imports only the
original two public dependencies; public imports and all existing signatures are preserved. The
item's DAG proof is updated to this route. No shared definition, source-library module, target,
or consumer is changed.

Validation: `lcompile.py` compiled the complete proof successfully in 27.8 seconds (exit code
zero). Profiling options used for timing have been removed. The assigned theorem signature was
compared against the original source and is unchanged.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.ordinaryQuotientPullback_successor` (node
`lem-trf-ordinary-quotient-pullback-successor`). No holes remain in the item and no holes or
split statements are added. This is a proof, not a decomposition.

## No longer needed

No existing imports, nodes, or modules are withdrawn. All four original declared dependencies
remain used. The DAG now also explicitly records the existing finite tensor-section and
transition definition node `def-weil-integral-reduction-tower`, already in the transitive import
closure, and the proved scalar-unit normalization in `lem-trf-coherent-quotient-ordinary-lift`.
The proof does not need a separate equality between `coefficientOrdinaryQuotient` and
`unrestrictedIntegralTransition`, nor the `M.transition` field: the compatible projections of
the ordinary adjunction unit and `M.unit_tensor` suffice after tensor-generator extensionality.
This prunes that proposed intermediate calculation without withdrawing the definitions or their
other uses.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan compared arbitrary finite quotient sections. Testing instead on generators
`1 tensor x` makes compatibility of the ordinary limit cone sufficient. The proof keeps the
assigned statement, arbitrary independent scheme and coefficient universes, all levels including
zero, and all complexes without flatness or boundedness assumptions. No statement repair or
unit-route change is needed.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
