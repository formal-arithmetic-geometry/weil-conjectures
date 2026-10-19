## What changed

Proved `AlgebraicGeometry.rational_tangent_cotangent_duality` in
`Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality`, with its statement unchanged.
The proof uses the existing rational-point identifications, constructs the map on
cotangent quotients using Mathlib's `Ideal.mapCotangent`, and proves its k-linearity
from compatibility of the structural stalk maps. Naturality follows by reconstructing
local-spectrum morphisms from their stalk maps and comparing epsilon coefficients.
Three proved private helpers handle structural compatibility and local-spectrum
reconstruction/naturality. No definitions, public interfaces or imports changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.rational_tangent_cotangent_duality`
(node `lem-sc-rational-tangent-cotangent-duality`).
No holes added or split off. No sorry remains in the delivered module.

## No longer needed

None. The existing proof-dependency import is used, and all the node's declared
mathematical dependencies remain part of the proof. No modules or nodes pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The proof follows the existing two-step
DAG argument; Mathlib's cotangent quotient API supplies its quotient-map construction.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
