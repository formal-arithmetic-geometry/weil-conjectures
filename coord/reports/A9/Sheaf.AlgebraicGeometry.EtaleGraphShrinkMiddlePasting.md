## What changed

Replaced the body of `AlgebraicGeometry.Etale.etaleGraphShrinkMiddlePasting`
by a complete assembly of the two projection pastings. Its signature and public
import are unchanged. The new proof imports are
`Sheaf.AlgebraicGeometry.EtaleGraphShrinkFirstLeg` and
`Sheaf.AlgebraicGeometry.EtaleGraphShrinkSecondLeg`.

Added `Sheaf.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords`. It constructs
the intersection graph and proves its properness; constructs the inclusion of
smaller intersections; proves both projection equations, its Cartesian square,
openness, the graph factorization, and the ambient open factorization; and defines
the literal intermediate derived word, its two leg isomorphisms, and its inverse
shrinking triangle. `graphMiddle_eq_intersectionLegs` is proved by expansion of
the existing middle word, componentwise functoriality, and associativity.
No data is chosen from an unproved existence statement.

Validation: `lcompile.py --all` compiled all four modules successfully, in
42.4, 41.8, 43.5 and 43.0 seconds respectively (each below 60 seconds).
The original theorem signature was compared with the live source and is unchanged;
all delivered DAG dependency references exist and their proof-step unions match.

Added the two public projection-pasting statements, one per module. Each is
strictly one half of the original intersection argument. The first involves the
first inverse triangle and does not mention the second-neighborhood triangle.
The second involves the second triangle and does not mention the first-side
transport. Neither mentions `graphMiddle` in its type or assumes the original
pasting theorem. Their common intermediate word and its shrinking map are explicit.
The original proof combines these halves using categorical associativity.

## Proved and sorry left

This is a decomposition, not a fully discharged proof. One original hole is
removed, in `AlgebraicGeometry.Etale.etaleGraphShrinkMiddlePasting`
(node `lem-pur-etale-graph-shrink-middle-pasting`), and two holes are added:

- `AlgebraicGeometry.Etale.etaleGraphShrinkFirstLeg`, node
  `lem-pur-etale-graph-shrink-first-leg`.
- `AlgebraicGeometry.Etale.etaleGraphShrinkSecondLeg`, node
  `lem-pur-etale-graph-shrink-second-leg`.

Actual direct hole counts: zero in the item module, zero in the intersection-word
module, and one in each projection-pasting module, hence two in this delivery.
Each remaining proof is exactly `:= by sorry`, with its source and complete proof
in words in the docstring and node. No private theorem or definition has a hole.
The geometric construction, all its displayed properties, the middle-word
factorization, and the assembly from the two projection statements have complete
Lean proofs. The net direct-hole change of this decomposition is +1.

## No longer needed

No existing declaration or module is withdrawn, and no original public import
is removed. None of the original mathematical dependencies is pruned globally:
`lem-pur-etale-graph-neighborhood-geometry`,
`lem-sf-etale-locally-closed-graph-model`, and `def-pc-fibre-product` support the
intersection construction; `lem-pur-etale-proper-open-exchange-cube`,
`lem-cbc-extension-zero-composition`, and
`lem-amb-natural-transformation-whisker-exchange` remain dependencies of the two
projection pastings. The item's immediate proof dependencies now name the
intersection-word definition and the two projection statements instead.
There are no unused added proof imports.

## Where the brief, the DAG or earlier work was wrong

No false statement, definition repair, or unit-route change was found. The
original plan's phrase “apply horizontal exchange pasting ... to each ...
projection” hides two separate normalized equations. The exchange-cube theorem
states horizontal pasting for the chosen family, while the graph words use
Cartesian exchanges with the identity-open normalization and explicit open
compositors. No existing graph-specific theorem supplies either displayed leg
normalization. The decomposition exposes these subcalculations and completes
their geometric setup and the final combination, without claiming them proved.

The shorter-route search used LeanFinder, Loogle, LeanSearch and repository and
Mathlib searches. The hits were ordinary neighborhood inclusions, generic
whiskering, and derived-functor coherence; they did not identify these specified
proper/open graph triangles. The existing locally closed extension coherence
uses arbitrary ring sheaves on the pro-etale site of Noetherian schemes, so it
does not apply to this unrestricted small-etale statement.

Edge cases checked in the statements and construction: identity shrinking,
empty intersections (including empty source), and the zero coefficient ring.
The pullback lifts and triangle/compositor words still exist in each case;
there is no nonemptiness, quasi-compactness, Noetherianity, or boundedness
hypothesis. The fixed unit `sk-prop-sf-cbc` and all existing target statements
are preserved.

## New nodes

`def-pur-etale-graph-shrink-intersection-words` records the actual intersection,
its proper graph and shrinking map, the two leg words, their middle-word
factorization, and the common inverse intersection triangle. All proofs in its
Lean module are complete.

`lem-pur-etale-graph-shrink-first-leg` states the first-projection instance of
horizontal triangle pasting, together with the unchanged first-side transport.
It remains a named hole and is independent of the second projection equation.

`lem-pur-etale-graph-shrink-second-leg` states the second-projection instance,
comparing the intersection shrinking triangle with the neighborhood shrinking
triangle. It remains a named hole and does not use the first projection triangle.

All three nodes inherit the item's chapter and unit and cite the product-graph
extension of the Stacks 0F7J calculation, with 0F7D supplying horizontal pasting.
The existing item node now records exactly the factorization and assembly used
by its Lean proof. There are no change records: no existing definition,
statement, visibility, or public import was changed.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
