## What changed

Filled `AlgebraicGeometry.Etale.SfP1Transport.exchangeIsoTransport` in the assigned
module without changing its statement or its original public import.

The proof first establishes a source-change identity for ordinary derived exchange
by adjunction transposition. The square comparison follows from pullback-compositor
associativity; naturality, the composite-counit formula and the adjunction triangle
finish the transpose. Stacked-square exchange pasting gives a second expression for
the same outer rectangle. The two expressions yield the required forward equation.
The already proved `unit_comp_pushPull` identifies its coefficient comparison with
the inverse of the specific `pushPull` from the statement. Isomorphism cancellation
then gives the inverse ordinary-exchange equation. Finally, naturality of proper
forget-supports and `proper_self_exchange_forget_supports` recover the supported
exchange equation.

The local transport helpers compare whole functors and isomorphisms before taking
components, avoiding repeated unfolding of the derived-category constructions.

Added only private, proved helpers in the item module and private proof imports of
`ProperSelfExchangeForgetSupports`, `SfIsoPushPullUnitNormalization`,
`BaseChangeCube` and `CompactificationRefinementLowerStar`. Updated the item's DAG
proof and proof origin to record this calculation. No shared definition, existing
public interface, other module or other node was changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.SfP1Transport.exchangeIsoTransport`
(node `lem-sf-p1-exchange-iso-transport`).

Holes closed: 1 of 1. Holes added: 0. Holes remaining in the item: 0.
No statements were split off. Every added private helper is proved.

## No longer needed

None. No imports were removed and no nodes or modules were pruned. All five
original declared proof dependencies remain in the argument. The original public
import of `SfP1ChartExchange` remains necessary for `projectiveProjectionSquare`
in the public statement; its coefficient or chart-trace formulas are not invoked.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The existing plan suffices using the proved
proper forget-supports and isomorphism-unit normalizations, together with the
source library's general derived exchange and compositor formulas. No further
copy of the residual obligation is introduced.

The proof uses naturality, adjunction transposition and isomorphism cancellation
for arbitrary complexes. It adds no boundedness, nonemptiness, twist, trace or
coefficient-normalization hypotheses, and applies to the empty base and zero
coefficient ring. The unit's statement and realized route are unchanged.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
