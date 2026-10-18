## What changed

Proved `CompactT2.extremallyDisconnected_iff_projective_iff_section` in
`Sheaf.Topology.StoneanProjective` without changing its signature. Mathlib already
proves Gleason's equivalence and supplies the total-separatedness instance.
The section characterization is proved directly: lift the identity in one
direction, and take the second projection of a section of the compact closed
pullback in the other direction. The node's proof now records this route.
The unit's projectivity characterization and minimal-source route remain
represented by Mathlib's existing Gleason theorem.

## Proved and sorry left

Closed 1 hole:
`CompactT2.extremallyDisconnected_iff_projective_iff_section`
(node `det-pe-stonean-projective`). Added 0 holes. No `sorry` remains in any
delivered Lean module. No intermediate theorem was split off.

## No longer needed

Removed the explicit proof imports `Mathlib.Topology.Compactness.Compact`,
`Mathlib.Order.Zorn`, and `Mathlib.Topology.Homeomorph.Lemmas`. All APIs used by
the proof are already available through the existing public import
`Mathlib.Topology.ExtremallyDisconnected`.

The node no longer separately needs `lem-weil-pbc-zorn-lemma` or
`lem-weil-pbc-compact-hausdorff-bijection`: Mathlib's Gleason equivalence
encapsulates that argument. These nodes are Mathlib leaves and have no Sheaf
module to withdraw. The product-compactness and closed-subset-compactness
nodes remain dependencies for the explicit pullback proof. No library module
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing search log already found Mathlib's exact Gleason equivalence,
but rejected it because it did not state every clause of the conjunction
in one declaration. Combining it with an explicit pullback argument and the
existing total-separatedness instance proves the full assigned Lean statement.
No mathematical statement or definition was changed. As before this delivery,
the Lean signature expresses total disconnectedness; it does not separately
state the inverse-limit characterization of profiniteness described in the
node's prose. That characterization is not needed for this proof.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
