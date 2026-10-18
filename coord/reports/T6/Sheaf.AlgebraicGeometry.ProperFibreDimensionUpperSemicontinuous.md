## What changed

Proved `AlgebraicGeometry.isOpen_setOf_topologicalKrullDim_fiber_le` in
`Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous`, with its statement
and public imports unchanged. The proof follows all four existing DAG steps and
Stacks Project Tag 0D4I: the bounded local-dimension locus is open upstairs,
its complementary closed locus has closed image, the fibre dimension is bounded
exactly outside that image, and the complement is open.

The point comparison uses `Scheme.Hom.fiberHomeo`, `range_fiberι`, and a local
proved equality transporting `asFiber` across an equality of base points. The
supremum characterization uses the existing
`topologicalKrullDim_eq_iSup_topologicalKrullDimAt`. Its universal bound handles
empty fibres without any nonemptiness assumption. No Noetherianity or flatness
is introduced. No declarations, definitions, or signatures were changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isOpen_setOf_topologicalKrullDim_fiber_le`
(node `lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous`).
There are zero remaining holes in the delivered module and zero added holes;
no split-offs. This proof uses the existing declared dependency
`AlgebraicGeometry.isOpen_localFibreDimension_le`
(node `lem-weil-pbc-local-fibre-dimension-open`), whose proof remains `sorry` in
its unchanged module. Consequently this closes the assigned local hole, not
the transitive proof of upper semicontinuity.

## No longer needed

Removed the private import `Sheaf.Topology.DimensionSupremumLocalDimensions`,
a retired compatibility module that merely re-exports
`WeilConjectures.Topology.DimensionSupremumLocalDimensions`. The latter remains
imported directly and its theorem is used. No declared proof dependency is
pruned: the properness and locally finite type definitions, local fibre
openness, fibre identification, and dimension supremum theorem are all used.
No other modules or nodes are made unnecessary by this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancies. The initial imports included both the retired
Sheaf compatibility module and its replacement in WeilConjectures. Removing
the redundant import leaves the proof route unchanged, so no node update is
needed. The unit's statements and proof steps are preserved.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
