## What changed

Replaced the sorry in `WeilConjectures.commonProjectionOpenFactor` by an explicit
coefficient-comparison calculation. Private proved helpers transport the recorded
stage coordinates, preserve adjunction transposes, use the open unit and pullback
compositor, preserve the factored support identification, invert the open square,
and apply proper direct image before pasting the support square. The theorem's
signature and all existing public imports are unchanged.

Added the proof import `Sheaf.Paper.CommonProjectionOpenPullbackTensor`. Its single
statement concerns only the inverse pullback/tensor square at the open immersion,
with no open adjunction, proper image, or support identification. Its generic
`OpenPullbackTensorSquare` predicate is an explicit equation, with no postponed
data construction; keeping the coefficient-category parameters abstract avoids
repeated expansion of localization instances. The square is strictly
below the original open factor: the adjunction and the entire proper/support
pasting are proved in the item, rather than included in the new obligation.

Validation: both sandbox modules compile through `lcompile.py`; the final item
compile completed in 16.9 seconds with no diagnostics. The original theorem
signature was compared verbatim with the shared source and is unchanged. The
import-direction check accepts the new proof import. No profiler options remain.

## Proved and sorry left

Closed the original hole `WeilConjectures.commonProjectionOpenFactor`
(node `lem-sf-common-projection-open-factor`) from the new tensor/pullback square.
Added one hole: `WeilConjectures.commonProjectionOpenPullbackTensor`
(node `lem-sf-common-projection-open-pullback-tensor`). No sorry remains in the
item. This is a decomposition: one original hole closed, one strictly smaller
hole added; net hole reduction zero. Every private helper is proved, and no
existing declaration outside the item was changed.

## No longer needed

None. All original dependencies still supply operations, normalizations, tensor
comparison, factor definitions or endpoint comparisons used by the proof. No
module is withdrawn and no unit statement or step is bypassed. In particular the
ring-sheaf `OpenProjectionFactorCoefficientChange` and
`ScalarPullTensorCoefficientCoherence` do not supply the same finite/common-stage
maps and were not imported.

## Where the brief, the DAG or earlier work was wrong

The old proof text gave the mathematical argument but named no declaration for
the tensor/pullback square with the newly constructed canonical natural
`commonProjectionTensorComparison`. The delivery formalizes all of the subsequent
adjunction, compositor, proper-image and support calculations and states precisely
that remaining square. The existing normalization declarations are used as stated;
no statement or definition repair is required.

Edge cases checked for the new statement: empty opens and schemes, zero inputs,
and identity pullbacks have exactly the same representative, unit and inverse
cancellation equations. No faithfulness of the inclusion, invertibility of a
proper projection, or arbitrary choice of coefficient comparisons is assumed.
The unit record `sk-rem-sf-pf-done` has no realized statement or steps to bypass.

## New nodes

`lem-sf-common-projection-open-pullback-tensor` records the inverse tensor/pullback
square on two rational objects at E. Its docstring and node give the finite-stage
representative argument, the precise normalizations to use, source and searches.
The blueprint search found no matching imported node; the ancestor command
returned None, as it already does for the item's module-name ancestry. No change
record is needed because existing interfaces are unchanged.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
