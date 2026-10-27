## What changed

Proved `etaleCompactScalarUnit` from normalized scalar left unitality and the
scalar/pullback unit equation. Added proved generic representative transport,
composite left-unit, and tensor-isomorphism unit-detection lemmas. Added the
site scalar left-unit proof by adapting the existing right-unit representative
argument. The pullback-unit equation follows from the binary scalar/pullback
tensor square; that square is the single split-off statement.

The item keeps its existing public declarations, definitions, and public imports.
Two private proof imports supply the new unit results. Composition, refinement,
and open-restriction proofs are preserved. The site representative is one private
explicit definition with proved component and K-flat invertibility lemmas; the
generic formulas avoid repeatedly expanding ordinary and derived adjunctions.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etaleCompactScalarUnit` (one of the item's two
original holes). This is a decomposition with one new lower hole, not a net
hole reduction. The left scalar tensor-unit clause and the generic unit
assembly are fully proved.

Remaining in the item: `AlgebraicGeometry.Etale.etaleCompactScalarCoherence`
(node `lem-pur-etale-compact-scalar-coherence`). Its full existing statement
and source proof plan remain unchanged.

Added: `AlgebraicGeometry.Etale.etaleScalarPullback_tensor`
(node `lem-pur-etale-scalar-pullback-tensor-coherence`), in its own module.
This binary tensor compatibility for arbitrary geometric pullback has no
compact support, proper pushforward, refinement, composition, or unit conclusion.
It is a strict constituent of the original projection/unit argument.
All other new theorems are proved, with no local `sorry`. The representative
formula and invertibility checks use proved generic APIs to keep the site
specialization within the file compile limit.

## No longer needed

No existing imports, nodes, or modules are pruned. Redundant direct Mathlib imports
were removed from the new generic proof modules. The unfinished coherence
proof still needs its stated dependencies. The unit proof uses elementary
monoidal unit transport instead of constructing a complete general ringed-topos
comparison system, but that system remains in the projection proof plan.

## Where the brief, the DAG or earlier work was wrong

The generic ringed comparison system does not directly specialize the published
chosen scalar adjoint and geometric pullback comparisons in one application.
The concrete binary tensor square records the needed normalization step.
Its source proof uses flat K-flat representatives and ordinary balanced tensor
maps, without assuming flatness of B over A. Edge cases checked in the argument:
identity maps, zero rings, zero inputs, empty schemes, and nonflat ring quotients.

## New nodes

`lem-pur-scalar-left-unit-transport`: proved categorical representative calculation.

`lem-pur-scalar-left-unit`: proved normalized scalar left unitality on the site.

`lem-pur-composite-left-unit-coherence`: proved pasting of left-unit laws.

`lem-pur-tensor-iso-unit-coherence`: proved unit detection from tensor compatibility
for an invertible natural transformation.

`lem-pur-etale-scalar-pullback-tensor-coherence`: binary tensor square, the one new hole.

`lem-pur-etale-scalar-pullback-unit-coherence`: proved assembly of the pullback unit
square from the binary square and constituent unit laws.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
