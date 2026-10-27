## What changed

Proved `AlgebraicGeometry.Scheme.RingedRestrictionExchange.exchange_chainUnit` from
`UnboundedExactTower.localized_mate_cochain_normalization` and
`StrictTowerRingedSquare.ambientSquare_localization`. A proved private helper identifies
`cochainUnit` with the existing `chainComparison`; another cancels the inverse lower
localization factorization. The ordinary and derived mates are the specified constructions.

The general calculation is specialized first to the exact project module categories with
six arbitrary functors, and then to the concrete ringed operations. This preserves the native
instances and category expressions without unfolding concrete tensor objects. All helpers
are proved. Existing public definitions and declaration signatures are unchanged.

Added only proof imports of `ProEtaleRingedSquareLocalization` and
`UnboundedExactAdjunctionSquare`. Updated the existing node's proof and proof origin.
The complete module passed the remote single-file compile in 9.9 seconds; diagnostic options
have been removed from the delivered source.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.exchange_chainUnit`
(node `lem-sf-ringed-exchange-chain-unit`). Holes added: zero. Holes remaining in the delivered
module: zero. No statement was split off.

## No longer needed

No import, node or module is pruned. Both original public imports support the existing
operations, and both declared proof-dependency modules are used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The node named the private
`localized_mate_cochain`; its public wrapper `localized_mate_cochain_normalization` supplies
exactly the required calculation. Direct specialization exceeded the kernel limit because
of conversions between the native and inherited preadditive structures and between complex
functor applications. Specializing to the exact project categories while the functors are
still variables resolves this without changing any definition, hypothesis, conclusion, or
unit route.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
