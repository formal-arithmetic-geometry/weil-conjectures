## What changed

The item module now composes two explicit proof interfaces: an unmarked bounded finite-free
lift and a separate prescribed-marking comparison. The item imports only its statement imports
and these two proof modules. The two new modules are
`Sheaf.RingTheory.UnmarkedFiniteFreeLift` and
`Sheaf.RingTheory.MarkedFiniteFreeLiftCompatibility`.

## Proved and sorry left

The parent declaration `DerivedCategory.exists_marked_finiteFree_lift_of_nilpotent` is reduced
to the two strictly smaller named statements below. No existing sorry was closed by a direct
construction. The following new theorem holes remain:

- `DerivedCategory.exists_unmarked_finiteFree_lift_of_nilpotent`
  (`lem-weil-pbc-nilpotent-marked-free-complex-lift-unmarked`): construction of the
  bounded finite-free lift and its unmarked isomorphisms.
- `DerivedCategory.exists_marking_compatible_finiteFree_lift`
  (`lem-weil-pbc-nilpotent-marked-free-complex-lift-marking`): the cone-coordinate homotopy
  proving compatibility with the prescribed derived marking.

## No longer needed

The item module no longer imports the proof-only cone-lifting, acyclic-lifting, strict-map,
cokernel, projective-class splitting, finite-projective, bounded-flat, K-projective,
homology-sequence, or independent-coefficients modules directly. Those dependencies are
encapsulated by the two new interfaces. The retained public imports are required by the item
signature.

## Where the brief, the DAG or earlier work was wrong

The original node presented the full cone construction and marking calculation as one theorem,
while the available interface is naturally split into construction and comparison. No statement
or target declaration was changed.

## New nodes

`lem-weil-pbc-nilpotent-marked-free-complex-lift-unmarked` records the unmarked lift interface.
`lem-weil-pbc-nilpotent-marked-free-complex-lift-marking` records the remaining marking
comparison. Both are in the item chapter and unit and are stated in separate modules.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
