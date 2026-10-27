## What changed

Proved `AlgebraicGeometry.Scheme.etale_line_frame_transition_units` without changing
its statement or any existing definition. Private helpers establish componentwise
inverse identities, linearity, naturality and cancellation of frame changes.
The transition unit is constructed explicitly from the values at 1 of the forward
and reverse changes. Naturality proves its action on every test object; cancellation
proves the triple cocycle, and evaluation on the diagonal proves normalization.
The ordinary descent maps conjugate the existing `Modules.smulHom` automorphisms
by the canonical tensor-unit isomorphisms. A private adjunction argument proves
compatibility with scalar pullback. Added the private proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.Defs` for that existing scalar API.
Updated the item's node to record this adjunction argument and its already proved
tensor-unit dependency. No other existing module is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.etale_line_frame_transition_units`
(node `lem-trf-etale-line-frame-transition-units`). No holes added or split off.
No `sorry` remains in the delivered Lean file.
The final single-file compile passed without warnings in 13.2 seconds.

## No longer needed

No original import or declared dependency was removed. No module or node is
withdrawn. The direct computation on locally represented tensors in steps 5--6
is unnecessary: the existing scalar pushforward and naturality lemmas, transposed
under the tensor adjunction, prove the same pullback identity.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The cover and sheaf hypotheses are unnecessary for the
frame calculations but are preserved verbatim. In particular, diagonal
normalization is proved only after pulling back along the diagonal; no identity
of the transition unit over the whole self-overlap is asserted.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
