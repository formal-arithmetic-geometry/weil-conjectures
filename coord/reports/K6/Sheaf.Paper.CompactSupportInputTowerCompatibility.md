## What changed

Proved `WeilConjectures.compactSupportInput_completed_tower` in
`Sheaf.Paper.CompactSupportInputTowerCompatibility`, preserving its statement and
public import. Private proved helpers compare the ordinary and derived restriction
compositors and their adjoint mates, and assemble the native completed coefficient
tower. The existing evaluation isomorphisms give a map to the specified integral
tower; naturality and cancellation prove the assertion for every comparable pair.
Only this module and its own proof-route node are changed.

Proof imports expose the existing private scalar-adjunction transition calculation
in `CompactSupportReductionTower` and `sectionTransitionAdjoint` in
`IntegralReductionTransitionComparison`. The coefficient-transition theorem supplies
the completed evaluation compatibility. `SfIntegralReductionTower` supplies its
sequence construction, and `MapDerivedCategoryMate` supplies derived compositor
naturality. All newly introduced private helpers are fully proved.

The existing node `lem-weil-compact-support-coefficient-transition` is used as a tool
from `sk-def-sf-operations`: its precise completed restriction/evaluation equation
is needed here and is not replaced by another unit's route. No unit statement or
realized step is bypassed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.compactSupportInput_completed_tower`
(node `lem-coef-compact-support-input-tower-compatibility`).
No holes remain in the delivered module. No holes or split-off statements are added.
The complete proof compiled without warnings in 24.8 seconds before removal of
the redundant import; the delivery checks validate the final packet.
The proof uses existing stated dependencies, including the coefficient-system
existence theorem, as authorized by stage 3.

## No longer needed

No original import is removed. A redundant proof import of
`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` was removed because
`CompactSupportCoefficientTransition` already publicly imports it. The proof does
not need the planned direct dependency
`lem-coef-sequence-roos-model` (`Sheaf.Paper.CoefficientSequenceRoosModel`): identity and
composition of native transitions follow directly from exact localization, and
`NatTrans.ofOpSequence` supplies compatibility at all indices. Its direct edge is
removed from this node; no module is withdrawn.

The direct edge to `lem-coef-normalized-dvr-kflat-transition` is redundant here:
`sectionTransitionAdjoint` already incorporates that comparison. This node remains
needed transitively by `IntegralReductionTransitionComparison`; it is not claimed
as globally pruned. No other planned mathematical dependency is discarded.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement needs no repair. The planned Roos-model invocation is
unnecessary for transition composition. The proof-route node now records the
actual native-tower argument and the existing coefficient-transition theorem.
The generic restriction and mate lemmas avoid expanding completed coefficient
constructions during elaboration. No shared definition, target statement, source
library declaration, or consumer module is changed.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
