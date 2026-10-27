## What changed

Proved `AlgebraicGeometry.exists_invariant_affine_of_finiteLocallyFree_groupoid`
without changing its signature or any public import. The proof constructs the arrow
relation using Mathlib's scheme pullback point-lifting theorem, then constructs the
invariant interior `H(E)` as the complement of the source-image of the target-preimage
of the complement of E. A proved private helper `finite_subset_basicOpen` applies
prime avoidance to choose a principal open containing the finite orbit. The existing
proved norm-locus theorem makes its invariant interior affine.

Replaced the private proof import of
`WeilConjectures.FieldTheory.CommonExtensionFields` with
`Mathlib.AlgebraicGeometry.PullbackCarrier`. Updated the item's DAG proof to match,
using the already recorded Mathlib leaf
`lem-weil-pbc-scheme-pullback-compatible-point`. No shared interfaces or other modules
changed. The recorded unit route is preserved.

The proof follows Stacks Project Groupoids Tag 03JE, `lemma-find-invariant-affine`,
read in `literature/stacks-project/groupoids.tex`. The prime-avoidance ideal consists
of sections whose basic opens lie in B; closure under sums and multiplication is
proved explicitly. Only the source needs to be closed and have finite fibres, both
consequences of the supplied finite locally free hypotheses. No separatedness,
Noetherian, degree, or residue-field assumptions were added.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_invariant_affine_of_finiteLocallyFree_groupoid`
(node `lem-sfb-locally-free-groupoid-invariant-affine`).
Added 0 holes; split off 0 statements. No `sorry` remains in the item.
Both the private helper and the main proof are complete.
The final single-file server compile passed cleanly in 3.2 seconds.

## No longer needed

Removed proof import `WeilConjectures.FieldTheory.CommonExtensionFields` and direct
proof dependency and obsolete top-level `tool_uses` entry
`lem-weil-common-extension-fields`. Mathlib's already proved
`Scheme.Pullback.exists_preimage_pullback` handles the common-residue-field lifting
inside a fibre product. No other planned dependencies or modules were pruned.
All five mathematical steps remain: orbit relation and finiteness, invariant
interior, principal-open selection, the final invariant open, and norm affineness.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's common-field construction was unnecessary
because point-lifting already has an exact Mathlib lemma and a recorded leaf.
The invariant interior can be defined in the source-image orientation from the
start, eliminating the later inversion exchange of the two image formulas.
The original declaration docstring describes the equivalent target-image
orientation; the updated DAG describes the orientation used by the Lean proof.

Edge cases checked: the orbit is nonempty by the identity, so prime avoidance has
a valid chosen index. Empty schemes have no supplied point x. Basic-open ideals
include the zero section and multiplication by arbitrary sections; no assumption
that B is affine is used. Inseparable and nonclosed points are covered by the
scheme pullback-point theorem, without any rational-point assumption.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
