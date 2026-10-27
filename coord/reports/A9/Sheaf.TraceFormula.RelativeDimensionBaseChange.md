## What changed

Proved `AlgebraicGeometry.pure_relative_dimension_base_change` in
`Sheaf.TraceFormula.RelativeDimensionBaseChange`, following the existing four-step DAG plan
and Stacks Tags 02NK and 02FY. Its statement, docstring, public imports and existing proof
imports are unchanged. No definitions or consumers change.

The proof converts pure dimension of each original fibre into constant local dimension with
`topologicalKrullDimAt_eq_of_equidimensional_open`, transfers that equality using
`fibre_dimension_after_base_change`, and recovers pure component dimension with
`topologicalKrullDim_component_eq_of_constant_local_dimension`. Mathlib supplies stability
of locally finite type morphisms and local Noetherianity over residue fields. Two fully
proved private helpers transfer component dimensions along a homeomorphism and identify
an arbitrary fibre point with its canonical `asFiber` representative. All existing proof
imports are used. The DAG route and dependency set already describe this proof, so no node
change is needed.

The file compiled cleanly on the server in 4.9 seconds. A separate `#print axioms`
compile reported exactly `propext`, `Classical.choice`, and `Quot.sound` (6.2 seconds). Empty original fibres are never
queried without a point witnessing nonemptiness. Empty base-changed fibres have no
components; the argument actually establishes their pure-dimension condition too. The
case `d = 0` uses precisely the same finite local-dimension criteria.

## Proved and sorry left

Closed one of one holes: `AlgebraicGeometry.pure_relative_dimension_base_change`
(node `lem-trf-relative-dimension-base-change`). Zero holes remain in the item; zero holes
were added or split off. Both private helpers are proved completely.

## No longer needed

None. All existing imports and all declared proof dependencies remain necessary and are
used. No nodes or modules are withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The open-component dimension criteria are stated on an
open subspace, so their application with the top open requires explicit homeomorphism
transport. The fibre-dimension comparison is stated at canonical `asFiber` points, so a
small proved identification is needed to apply it to arbitrary points of a fixed fibre.
These are elementary glue within the existing route, with no new proof obligations.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
