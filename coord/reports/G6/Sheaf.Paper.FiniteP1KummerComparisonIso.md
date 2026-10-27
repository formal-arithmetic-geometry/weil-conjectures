## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_kummer_comparison_iso`
with an explicit composite of existing isomorphisms, without changing its signature.
The first composite is exactly the isomorphism whose hom defines `SpTowerP1.lineWord`:
`nuSingle`, the single-functor image of the supplied `c.line`, the inverse
`lineEvaluation`, and the inverse evaluation/single comparison, with the exact
shift comparisons at the two ends. Its inverse identifies the evaluated tower
line with intrinsic realization of the ordinary positive shifted Tate line on X.
The inverse of `geoP1TwistPullback` along `e.hom`, mapped through intrinsic derived
realization, completes the comparison with the pullback of the twist on P¹.
The exponent is a unit on P¹ by taking a power of `hS` and pulling back along
its projection. The DAG now records these two explicit compositions. Added a proof-only import of
`Sheaf.AlgebraicGeometry.FiniteP1UnitOnPullback` for the unit transport.
The first remote compile passed in 8.5 seconds; delivery checks validate the final packet.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.finiteP1_kummer_comparison_iso`
(node `lem-sfb-finite-p1-kummer-comparison-iso`).
No holes remain in the item; zero new holes and zero split-off statements.

## No longer needed

No modules or nodes are withdrawn. All three existing public imports are retained
as part of the module's interface. The theorem does not need
`finiteP1_coefficient_adjunction_coordinates`, any Chern-boundary compatibility,
or the projective-line cohomology/decomposition theorem: it only uses the
existing definitions and normalized comparison isomorphisms in those modules.
The original three declared dependencies remain used. No new intermediate
comparison module is needed.

## Where the brief, the DAG or earlier work was wrong

The old node's single proof step described the comparison without spelling out
its construction. The supplied `CoefficientCoordinates.line` and the already
implemented `lineWord` construction contain all the needed line comparison data;
no further existence or Kummer class theorem is required for this `Nonempty`
statement. The proof does not identify any Chern arrow, which belongs to the
separate boundary-transport obligation. There is no statement correction.
The construction also applies to n = 0, empty schemes, and the zero coefficient
ring: no cancellation, nonzero hypothesis, or choice of generator is used.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
