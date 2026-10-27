## What changed

Filled `AlgebraicGeometry.invariant_intersection_affine_descent` using the canonical
flat intersection-section comparison and affine flat descent. Added proved private
helpers for functoriality of intersection section maps, their preservation of
isomorphisms, tensor-spectrum comparisons, and constructing transport data from
a unital associative action. Removed the unused proof import `Mathlib.RingTheory.RingHom.Flat`. Public signatures
and definitions stay unchanged.
The node records the implemented double-base-change proof of the cocycle.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.invariant_intersection_affine_descent`
(node `lem-a1-invariant-intersection-affine-descent`). No new holes, no split-off
statements, and no remaining `sorry` in the delivered module. Its existing
flat section-comparison dependency is used as stated.

## No longer needed

Removed the unused proof import `Mathlib.RingTheory.RingHom.Flat`. No module is withdrawn. The following planned proof dependencies
are not needed by this proof:

- `lem-a1-subspace-ring-restriction-unit-coherence`: the defining adjunction unit
  proves functoriality directly for the particular intersection maps already in
  the statement. Its module is `Sheaf.Topology.SubspaceRingRestrictionUnitCoherence`.
- `lem-weil-pbc-flat-ring-map-iff-flat-affine` and
  `lem-weil-pbc-flat-ring-map-comp`: the triple comparison is obtained by applying
  the section theorem twice with the same flat map R→A, avoiding a separate
  flatness argument for R→A⊗A. The former is a Mathlib leaf in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`; the latter is a Mathlib leaf in
  `Mathlib.RingTheory.RingHom.Flat`.
- `lem-weil-pbc-flat-morphism-base-change` (Mathlib leaf in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`): each comparison uses the originally
  assumed flat morphism, so no new flatness instance is required.

These are removed from this node's proof dependencies; they may have other users.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics is sound. The transport-form Lean interface makes a
second application of flat base change to the double overlap more direct than
constructing all three tensor associativity comparisons explicitly. The affine
action's identity and cocycle are checked on spectra of the actual intersection
section rings, then its overlap is identified with the stated `Spec ψ`.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
