## What changed

Proved `AlgebraicGeometry.SectionCompactSource.supported_pro_exchange_isIso` in
`Sheaf.Paper.SectionSupportedProExchangeIso`, with its statement unchanged. Added private
proof imports of `SupportedConstantExchangeNormalization` (including its existing private
normalization lemmas), `SectionSupportedComparisonIso`, `Finite.BaseChange`, and
`OpenClosed.Exact`. No public import, definition, or consumer interface changed.

The proof obtains epic constant restriction from the underived étale open/closed short
exact sequence. After pulling back and applying site comparison, it cancels this epic map
to prove the actual comparison square from the existing exchange, gamma and scalar-unit
normalization equations. Finite étale base change and the supported-comparison
isomorphisms then prove invertibility by cancelling the two initial isomorphisms. The proof
handles empty closed sources and arbitrary base changes; it imposes no compactness condition
on the complementary open.

Updated the item's DAG proof and dependencies to match this argument. The unit record
`sk-prop-an` has no realized statement or step attached to this component, and the original
rank-one Thom Step 3 route is retained. No new nodes or statement/definition changes.

Searches used the required remote leanfinder, loogle and grep services and local source
searches. They found no direct general-coefficient pro-étale supported-exchange theorem.
The existing `scheme_normalization` and `comparison_square` use the special coefficient
ring of `PurityFiniteSetting`, but their existing private normalization equations already
apply to arbitrary A. This proof uses those equations without duplicating or changing them.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.SectionCompactSource.supported_pro_exchange_isIso`
(node `lem-pur-section-supported-pro-exchange-iso`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
No split-off statements. This is a proof from the existing library declarations, not a
new decomposition. Remote `lcompile.py` validation passed with exit code 0 in 13.1 seconds,
without warnings, against the current dependency overlay.

## No longer needed

No existing import was removed. The planned dependency
`lem-cbc-open-closed-recollement` (`Sheaf.AlgebraicGeometry.OpenClosedRecollement`) is not
needed: the proof uses the existing underived short exact sequence
`lem-weil-pbc-open-closed-short-exact` (`WeilConjectures.SixFunctors.OpenClosed.Exact`)
directly to obtain the epic restriction. Its derived distinguished-triangle construction
is unnecessary here, so it was replaced in this node's proof dependencies. This makes no
claim that the recollement module is unused by other nodes or targets.

All other originally declared proof dependencies are used:
`lem-pur-supported-constant-exchange-normalization`,
`lem-pur-section-supported-comparison-iso`, and `lemma-weil-pbc-finite-exchange`.
No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned argument is correct. The normalization module's public combined theorems are
specialized to purity coefficients; applying them directly would not prove the arbitrary
finite-ring statement. Their already proved arbitrary-ring normalization equations supply
exactly the needed calculation. The derived recollement dependency was stronger than needed;
the existing underived exact sequence suffices. No target or existing signature changed.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
