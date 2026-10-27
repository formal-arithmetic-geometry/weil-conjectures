## What changed

Moved the three concrete strict tower, quotient-unit, and summand definitions into the
shared `CompletedKoszulTensorQuotientAugmentationData` module. Added statement-only
existence and uniqueness components, then proved the assigned `completedKoszulTensorQuotientAugmentation`
by assembling those two components. The target statement and its hypotheses are unchanged.

## Proved and sorry left

The assigned theorem `completedKoszulTensorQuotientAugmentation` is proved. Two strictly
smaller components remain as named statement-only theorems: `completedKoszulTensorQuotientAugmentation_exists`
(new node `new-y2-completed-koszul-tensor-quotient-augmentation-exists`) and
`completedKoszulTensorQuotientAugmentation_unique`
(new node `new-y2-completed-koszul-tensor-quotient-augmentation-unique`). The data module
contains no sorry. Thus one upper hole is closed and two lower holes are split off.

## No longer needed

The assigned theorem no longer directly imports or uses the original proof-dependency
modules; those dependencies are retained by the existence component's recorded route.
No unit-route module was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original item combined the construction and its uniqueness in one theorem while the
construction has no direct library theorem. A compiling reduction requires separate
existence and uniqueness statements. The concrete definitions were also in the theorem
module, so they were moved to an acyclic shared data module for the split statement modules.

## New nodes

`new-y2-completed-koszul-tensor-quotient-augmentation-data` records the moved concrete
strict data definitions. `new-y2-completed-koszul-tensor-quotient-augmentation-exists`
records the existence component. `new-y2-completed-koszul-tensor-quotient-augmentation-unique`
records uniqueness from the unit and nonzero-summand formulas.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
