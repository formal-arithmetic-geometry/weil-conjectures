## What changed

Proved `WeilConjectures.IntegralProjectionReduction.OpenCoordinates.integralDatumPullCompositionReduction`
with its statement unchanged. Added proved private helpers for the finite normalized
compositor square, unary comparison evaluation, forward system-compositor evaluation,
and their pasted evaluation square. The proof lifts the conjugated system arrow through
the full whole-system reduction functor, identifies that lift with the datum compositor
using joint faithfulness of integral reductions, and applies reduction again.

Added proof-only imports of `IntegralProjectionPullEvaluation`,
`SystemPullbackCompositorEvaluation`, and `IntegralReductionJointFaithfulness`.
Full faithfulness is already publicly available through the coefficient-data imports. Updated the item's node proof and dependencies.
No shared interface or other existing module changes.

Validation: `lcompile.py` compiled the delivered module without warnings in 41.0 s.
The public theorem signature and public imports match the repository version exactly.
The module has no `sorry`, and all Lean lines are at most 100 characters.

## Proved and sorry left

Closed the item's one hole:
`WeilConjectures.IntegralProjectionReduction.OpenCoordinates.integralDatumPullCompositionReduction`.
Zero holes remain in the delivered module; zero holes were added or split off.
The existing unary evaluation and system-compositor evaluation statements are used as
stated dependencies; they are not reintroduced or renamed as new obligations.

## No longer needed

The item does not directly use `lem-sf-generator-reduction-coherence` or
`Sheaf.SixFunctors.GeneratorReductionStatement`: the existing unary pullback evaluation
and system-compositor evaluation statements suffice. Removed the generator-coherence
node from the item's proof dependencies. No preexisting import was removed, and no
module or declaration is withdrawn. The system realization data, full coherent
reduction and joint faithfulness remain needed.

## Where the brief, the DAG or earlier work was wrong

The old proof plan described redoing representative-level quotient calculations.
Those calculations already have more focused named statements:
`integralProjectionPullEvaluation` and `systemPullbackCompositorEvaluation`.
The latter belongs to the smooth-purity unit and is used only as a general
pullback-evaluation tool; the current unit has no realized proof steps to bypass.
The proof uses fullness only to lift a specified system arrow. Equality detection
is applied to two constructible integral arrows, never to arbitrary derived
system arrows. The rework entry and the item's existing declaration are preserved.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
