## What changed

Restored the quarantined module and repaired the final tensor-isomorphism composition in
`AlgebraicGeometry.smoothProper_dualizing_tensor_evaluation`. The upstream determinant
lemma concludes with `Scheme.Modules.exteriorPower`, while this theorem concludes with
`Scheme.Modules.exteriorSheaf`; the proof now introduces an intermediate `n'` and
transports `n.symm` using `Scheme.Modules.exteriorSheaf_eq_exteriorPower` before tensoring.
No declaration signatures, statements, definitions, or imports were changed.

## Proved and sorry left

Closed the existing compiler repair in
`AlgebraicGeometry.smoothProper_dualizing_tensor_evaluation` (zero `sorry` remains in the
item module). No new `sorry` declarations were added.

## No longer needed

None. The module's existing imports and DAG proof dependencies remain needed by the proof.

## Where the brief, the DAG or earlier work was wrong

The prior proof passed `n.symm` directly to `MonoidalCategory.tensorIso`, but `n.symm`
has an `exteriorPower` source whereas the target requires `exteriorSheaf`. The existing
compatibility theorem `Scheme.Modules.exteriorSheaf_eq_exteriorPower` supplies the
necessary equality; the repair inserts the corresponding shifted isomorphism.

## New nodes

None.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
