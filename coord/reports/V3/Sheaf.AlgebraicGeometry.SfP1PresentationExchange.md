## What changed

Proved `AlgebraicGeometry.Etale.SfP1Transport.presentationExchange` with its original
signature. Only the item module and its own DAG proof record change.

The proof first establishes proper forget-supports compatibility using the existing
compactification and refinement equations. Its private helpers follow the already
proved general private argument in `ProperSelfExchangeForgetSupports`; that module exports
only its flipped self-product specialization, which does not directly apply here.

For a square over an identity base map, adjunction transposition computes ordinary exchange
as the identity pullback comparison, the isomorphism unit, and direct-image composition.
The existing proved `unit_comp_pushPull` cancels that unit against the actual constructed
`pushPull`. The source theorem `derivedBaseChangeMap_cube` then pastes the two projection
squares and the two self-product squares. Finally naturality and proper forget-supports
compatibility give the stated compact-support equation.

Added proof imports supply the cube, identity pullback coherence, proper comparison API,
and existing isomorphism-unit normalization. All added helpers are private and fully proved.
The true-projection comparison is normalized at the isomorphism level before taking
components. The compact-support and ordinary exchange homs are also exposed before
their components are evaluated, and a generic categorical family performs the final
pasting. This avoids repeated kernel reduction of derived-functor instances. An explicit heterogeneous equality transports proper forget-supports across
`projection f true = pullback.snd f f`, avoiding expensive kernel reduction of derived
functor instances. The original comparison definition is preserved.
The public statements, definitions, attributes and imports are preserved.
Local instance settings reuse the canonical derived-category instances.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.SfP1Transport.presentationExchange`
(node `lem-sf-p1-presentation-exchange`). Added 0 holes; split off 0 statements.
The item module now contains 0 `sorry`s. No other existing module is changed.
Validation: the cleaned item compiled on the project server in 27.4 seconds with
no errors or warnings. All original public signatures, definition bodies and public
imports were compared with the current shared source and are preserved.
The proof uses existing declared dependencies; it does not claim those dependencies have
become independent of all remaining project holes.

## No longer needed

No original import or declared proof dependency is removed. No module is withdrawn.
No new intermediate obligation, Tate-line comparison, trace normalization, splitting-family
identity, boundedness assumption, or nonempty-base assumption is needed. The public chart
and coordinate imports remain because the original statement uses their square wrappers.
The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing DAG proof described the necessary calculation correctly, but did not name the
already proved `lem-sf-iso-pushpull-unit-normalization`. That theorem supplies exactly the
normalization of the constructed `pushPull`, so no further split is necessary. The updated
proof record names it and the existing proper-refinement comparison.

All equations hold for arbitrary derived complexes, including empty schemes and zero
coefficient rings: the proof uses only naturality, canonical comparison maps, adjunction
triangles, and invertibility from proper finite-coefficient base change.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
