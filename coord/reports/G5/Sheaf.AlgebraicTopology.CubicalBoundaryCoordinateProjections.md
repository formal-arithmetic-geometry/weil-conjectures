## What changed

Proved `IntegralLatticeCubical.boundary_coordinate_projections` without changing any existing
statement, definition, visibility, or public import. Added private proved helpers in the item
module and private imports of `Mathlib.LinearAlgebra.Finsupp.VectorSpace`, `Mathlib.Tactic.Abel`,
and `Mathlib.Tactic.Ring`.

The proof follows all eight steps of the node. Linear maps are compared on single basis cells.
Boundary squared is expanded over ordered pairs of distinct directions and cancelled by the
swap involution; a filtered-cardinality identity proves the opposite signs. Coordinate resets
commute with the relevant translations, giving the chain-map identities. Induction on a list
of coordinates calculates the projection product, including its empty list. The regular-orbit
isomorphism is Mathlib's product swap followed by `Finsupp.curryLinearEquiv`. The zero-rank
isomorphism uses the actual augmentation and section as inverse linear maps. Unsupported integer
degrees are handled by emptiness of the direction subtype.

Searches through LeanFinder, Loogle, the search wrapper's grep, and the local source found no
existing cubical identity that replaces these calculations. The general Finsupp equivalence and
freeness instance are used directly.

## Proved and sorry left

Closed one hole: `IntegralLatticeCubical.boundary_coordinate_projections`, node
`lem-sfb-cubical-boundary-coordinate-projections`.

Added zero holes; zero holes remain in the item module. No statements were split off.
The proof does not invoke `IntegralLatticeCubical.contraction` or any other unproved theorem.

## No longer needed

None. No imports were removed and no declared dependencies, nodes, or modules were pruned.
The existing parent-module import provides the actual chain constructions; its contraction
theorem is not used. The eight-step DAG proof and unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The Stacks alternating differential is a comparison source,
as the node already records; the coordinate and paired-face calculations are the node's
agent-written argument.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
