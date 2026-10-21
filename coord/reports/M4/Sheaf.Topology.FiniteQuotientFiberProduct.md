## What changed

Filled `Topology.finite_quotient_fiber_product` in
`Sheaf.Topology.FiniteQuotientFiberProduct`, keeping every declaration signature,
definition, and import unchanged. The proof implements the existing eight-step
DAG plan: the equalizer is closed; componentwise infima refine compatible spans;
quotient maps give the projections and transition maps; coherence reconstructs
each source point; the comap span for each middle quotient forces equality of
the images; a continuous bijection from compact to Hausdorff gives the requested
homeomorphism.

`DiscreteQuotient.exists_of_compat` is the exact Mathlib realization of the
stated dependency `lem-sfb-compact-discrete-quotient-realization`.
`DiscreteQuotient.eq_of_forall_proj_eq` packages the clopen separation argument
of `lem-weil-pbc-profinite-clopen-basis`; both are already available through the
module's imports. The source remains Stacks Topology Tags 08ZY, 005D, 0A2P, and
08YE, with the blueprint's compatible-partition construction. No route at the
unit level changes. Trivial discrete quotients handle empty spaces without a
nonemptiness assumption.

## Proved and sorry left

Closed the one original hole in `Topology.finite_quotient_fiber_product`
(node `lem-sfb-finite-quotient-fiber-product`). Zero holes remain and zero holes
were added. No statements were split off.

Validation: the complete module compiled through `lcompile.py` in 2.1 seconds.
A separate `#print axioms Topology.finite_quotient_fiber_product` compile also
passed in 2.1 seconds and reported exactly `propext`, `Classical.choice`, and
`Quot.sound`.

## No longer needed

None. No imports, nodes, or modules were removed. Both stated Mathlib-leaf proof
dependencies are used by their quotient APIs; there are no new proof imports.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG's partition argument is already
expressed by the existing `DiscreteQuotient` definitions, so no separate
partition-to-quotient comparison or additional intermediate theorem is needed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
