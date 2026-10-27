## What changed

Reduced `AlgebraicGeometry.Scheme.completeCompactSupportProetale_identity` to the
already proved proper-exchange identity and one ordinary open-exchange identity.
The original statement is unchanged. The proof obtains input and open-extension
completeness from the existing Koszul/quotient and completed-open comparisons,
and obtains the proper factor's finite origins from the existing open-extension
origin theorem. A proved private helper transports the ordinary open identity
through the completion unit, using the reflection universal property. The final
proof expands the two-factor exchange and cancels its adjacent identity maps.

Added `Sheaf.Paper.OrdinaryOpenExchangeIdentity`, containing only the missing
ordinary open identity statement. This lemma has no completed pullback,
compactification, proper pushforward, origins, completeness, generating tuple or
quasi-compactness hypothesis; it is strictly the open factor of the argument.
The original module privately imports it and `CompletedPullbackReflection`.
Updated the parent node's identity proof route and recorded the new node.

The current shared source already contains V5's clopen comparison proof. That
proof is preserved verbatim and is not counted as work of this delivery. No
existing statement, definition, attribute or public import was changed.

## Proved and sorry left

Closed one of the current item's seven holes:
`AlgebraicGeometry.Scheme.completeCompactSupportProetale_identity`
(node `thm-cbc-complete-proetale`). Added one smaller hole:
`AlgebraicGeometry.Scheme.cbcDatumOrdinaryExchange_identity`
(node `lem-cbc-ordinary-open-exchange-identity`). This is a decomposition, with
zero net holes closed, rather than a proof without remaining dependencies.

The following six holes remain unchanged in the item, all owned by
`thm-cbc-complete-proetale`:

- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_horizontal`
- `AlgebraicGeometry.Scheme.cbcRefinementMap_isIso`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_compactifications`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_refinement`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_vertical`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_composition_refinement`

The new lemma's docstring and node give its source and full mathematical argument.
The identity case includes the zero object and an empty open; no extra
boundedness, nonemptiness or finite-origin assumption is imposed on that lemma.

## No longer needed

None. No existing imports, modules, declarations or dependency nodes are removed.
The strict-tower realization and horizontal-exchange dependencies are unnecessary
for the newly written identity proof, which instead uses the proper identity and
the ordinary open unit equation. They remain needed by the planned proofs of the
unchanged horizontal and other coherence holes, so their parent dependencies
are retained. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent DAG gave a strict-tower route for all coherence assertions together.
Its identity subcase also admits the direct two-factor reduction written here:
the proper identity is already proved, and the completed open exchange retains
its ordinary-unit equation. The existing declarations did not provide the
ordinary open identity equation on this presentation, so that smaller equation
is stated separately. An attempted import of the strict-tower realization would
create a module cycle, because that realization module imports this item; this
delivery does not introduce that import.

The newest blueprint states the compact-support theorem with ordinary pullback
for constructible integral condensed coefficients. This delivery preserves the
existing auxiliary completed identity statement and makes no target or
coefficient-definition migration.

## New nodes

`lem-cbc-ordinary-open-exchange-identity`, in
`dag/nodes/sec-smooth-purity/lem-cbc-ordinary-open-exchange-identity.json`, owns
`Sheaf.Paper.OrdinaryOpenExchangeIdentity` and its sole theorem
`AlgebraicGeometry.Scheme.cbcDatumOrdinaryExchange_identity`. Its argument is the
identity specialization of the section-normalized right exchange, transposition
across the open adjunctions, and derivation with the fixed universal counits.
It is needed by the completed open identity helper and hence by the item.
There are no definition or statement change records and no adapted consumers.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
