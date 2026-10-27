## What changed

Proved `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.isomorphism_scalar_augmentation_cone`
from the normalized tower generator and cone-coordinate fields. The two existing public
definitions and the theorem signature are unchanged. Added proved helpers for tensor
linearity, tensor restriction, the two augmentation coordinates, the finite comparison square,
and the two scalar cone coordinates. Proof imports expose the existing proved tensor and Roos
coordinate helpers. Updated the item's proof plan to
match the argument through unit tensors and completed linearity. The self-contained tensor
section calculation is in the new proved module `Sheaf.Paper.CompletedTensorSectionProperties`,
so the item and its tensor API can compile separately within the 60-second per-file limit.
`lcompile.py --all` compiled both modules successfully, without errors or warnings.
The redundant direct tensor-construction import was removed; the public comparison API
already provides it, and the delivery check verifies the final imports.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.isomorphism_scalar_augmentation_cone`
(node `lem-weil-isomorphism-scalar-augmentation-cone`). No holes added, none split off,
and no `sorry` remains in either delivered module. The new theorem
`WeilConjectures.completedTensorSectionProperties` is fully proved. Its existing normalization/existence
dependencies remain available as stated library theorems; they are not claimed proved here.

## No longer needed

No existing public import or module is withdrawn. The proof does not use the theorem
`specifiedPullbackComparisonAlpha` (node `lem-weil-specified-pullback-comparison-alpha`):
the `ScalarPullbackStrictConeData` generator and coordinate fields are the exact strict data
needed. Its public import is retained for compatibility. The existence theorem
`isomorphism_scalar_tensor_kflat_model` is not invoked: the statement already supplies `b`
and its `CompletedFormula`. That module and node still supply the statement vocabulary.
No new K-flat resolution, derived descent, quotient reassociation, or separately proved
completed-coefficient projection square is needed. Completed-linearity reduces arbitrary
scalar tensors to unit tensors. No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's two explicit balancing steps can be replaced by completed-linearity: both
finite-level composites are maps over the completed coefficient sheaf. The final section
formula likewise follows from the unit instance of `CompletedFormula` and linearity.
No statement or definition is changed. The quarantined/rework entry was checked before
copying: the current item source is present, and this delivery preserves it and its Lean
attachment instead of withdrawing an absent/archive path.

The proof uses existing general tools from other units: the completed scalar tensor API
(`lem-weil-finite-free-completed-scalar-comparison`) and the proved generic
strict Roos coordinate calculation (`def-sf-additive-roos-map`). These supply only ordinary
sheaf tensor and explicit cone calculus; the item's own strict tower normalization remains
the comparison used throughout.

## New nodes

`lem-weil-completed-tensor-section-properties` records the fully proved conjunction
`WeilConjectures.completedTensorSectionProperties` in
`Sheaf.Paper.CompletedTensorSectionProperties`: completed tensor linearity and naturality
of unit tensors under site restriction. It is the elementary first step of the argument,
extracted to keep the actual sheafification computations out of repeated checks in the item.
No new sorry or change record is required; no existing interface was changed.
The helper is valid for the zero module, identity restrictions, and empty sites; its proof
uses only linearity, naturality, and preservation of one, without extra hypotheses.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
