## What changed

Filled the five theorem bodies in `Sheaf.Paper.SfFrameworkCommonStageDescent`.
Private helpers descend natural transformations from restrictions to the stage inclusions,
construct the normalized shift comparison, and verify its zero and addition equations.
The common-stage representative formulas prove additivity and Ω-linearity. The finite-stage
triangle criterion proves exactness. Existing StageSystem APIs handle transformation and
composition formulas; restriction to stages checks their shift compatibility.
Public statements, definitions, instances and imports retain their original interfaces.
Generic private unit and composition lemmas keep kernel checking independent of the large
concrete coefficient models.

## Proved and sorry left

Closed all five original holes:
`sfFrameworkCommonStageShift_existsUnique`, `sfFrameworkCommonStageDescent`,
`sfFrameworkCommonStageTransformations`, `sfFrameworkComposite_compatible`, and
`sfFrameworkCommonStageComposition`.
No new public statements or holes are introduced. The delivery module contains zero `sorry`.
The generic shift helpers and composite compatibility calculation compiled in separate diagnostics;
the final full-file and delivery checks are recorded by the delivery tool.

## No longer needed

None. The proof follows the existing node's argument and retains its statement dependencies.
No module or node is withdrawn; no imports are added or removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The canonical framework shift is chosen by a uniqueness
theorem, so shifted pair objects are propositionally equal to the displayed stage pairs.
The proof explicitly transports along these equalities instead of assuming that the
identity-normalized inclusion comparisons are definitionally identity arrows.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
