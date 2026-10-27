## What changed

Replaced the hole in `etaleGraphProductShrinkPasting` by composition of the lift-boundary
and final-square compatibility equations. The original statement, universes and public
import are unchanged. Its two new proof imports are private.

Added `EtaleGraphProductShrinkWords`, which constructs the middle boundary directly from
the composite graph triangle, open compositors, and the inverse exchange for the mixed
neighborhood inclusion. This construction uses neither B interchange nor Q interchange.
It constructs the inclusion `n` by a pullback lift and proves its openness and all five
projection/pasting identities, including `productBV_n` and `vf_BW`, for both selected sides.
No data is selected from an unproved existence theorem.

The two compatibility equations are in separate modules. The lift equation ends before
both final Q exchanges. The square equation uses the composite graph and mixed Q square;
it has no source support shrink or B interchange. Composition of these equations and
associativity give the original theorem in Lean.

Validation: the three new modules passed compilation through the required service.
The original theorem with the assembly proof compiled cleanly in 6.6 seconds.
A direct text comparison confirms that its original statement is unchanged.

## Proved and sorry left

Decomposition: one original hole closed and two strictly smaller holes added (net one more).

Closed: `AlgebraicGeometry.Etale.etaleGraphProductShrinkPasting`
(`lem-pur-etale-graph-product-shrink-pasting`). The item module has zero remaining holes.
All definitions and geometric equations in `EtaleGraphProductShrinkWords` are complete.

Added and remaining:

- `AlgebraicGeometry.Etale.etaleGraphProductShrinkLift`
  (`lem-pur-etale-graph-product-shrink-lift`), in `EtaleGraphProductShrinkLift`.
- `AlgebraicGeometry.Etale.etaleGraphProductShrinkSquare`
  (`lem-pur-etale-graph-product-shrink-square`), in `EtaleGraphProductShrinkSquare`.

Each has exactly `:= by sorry`, a source, and a full proof in words. The explicit middle
boundary is defined independently of these two assertions, so neither assertion is the
original conclusion with a renamed or repackaged hypothesis.

## No longer needed

No existing imports or modules were removed; no whole library module is claimed pruned.
The original proof dependencies are factored through the new support and compatibility
nodes. The product geometry and fibre-product API prove the new geometric equations.
The normalized exchange, proper-compositor, open-compositor and whiskering dependencies
remain needed by the two smaller pasting calculations.

The theorem `etaleGraphProductAmbientPasting` itself and the theorem
`etalePairwiseProductGraphNormalization` are unnecessary for this shrink calculation.
Their modules still provide the ambient and product constructions in its unchanged
public interface. The main node now records only the three nodes used in its actual
assembly proof; it no longer directly cites any of the eight old proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The old plan's cancellation step did not have a declaration for its intermediate mixed
boundary. The available cube theorem supplies elementary exchange pasting, rather than
that already assembled boundary. The new construction fixes that gap and separates the
inverse-B calculation from the final-Q calculation. No existing statement was weakened,
and no false statement or unit-route change was found.

Edge cases: all new maps are explicit pullback lifts; every equation is proved by
projections or cancellation of an open immersion. They require no points, nonemptiness,
distinct supports or nonidentity opens. The two remaining equations use the same unit
and pasting laws for identity and empty supports.

## New nodes

`def-pur-etale-graph-product-shrink-words`: the explicitly constructed mixed boundary,
its two input/output boundaries, and proved geometric equations. No holes.

`lem-pur-etale-graph-product-shrink-lift`: the inverse-B compatibility, before either Q
exchange. Its docstring and node specify the two horizontal pastings, graph-triangle
vertical pasting, and internal exchange cancellation.

`lem-pur-etale-graph-product-shrink-square`: the Q compatibility, after the explicit
mixed boundary. Its proof uses horizontal exchange pasting and open-compositor
associativity, independently of the source graph and both B exchanges.

No existing definitions or statements changed, so no change record or consumer
adaptation is required.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
