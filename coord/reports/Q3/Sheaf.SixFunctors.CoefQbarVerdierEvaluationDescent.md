## What changed

Replaced the hole in
`WeilConjectures.CoefQbarVerdier.descendedEvaluation_equations` with a categorical
assembly proof. The original definitions, theorem statements, and public import
are retained. Added private proved helpers for composition and inversion of
dinaturality, finite-inclusion naturality, transition pasting, the stage cocycle,
and the contravariant comparison across a transition.

The proof first obtains the descended omega square from the finite omega tower
and the stage cocycle. It proves evaluation naturality on finite inclusions and
stage-transition isomorphisms, then factors every quotient arrow into these
pieces. All comparison transports use the recorded stage system.

Added proof imports of `BilinearCoefficientDescent` (including its private cocycle
helper), `CoefQbarVerdierTensorInclusion`, `CoefQbarVerdierFiniteEvaluationStage`,
and the new `CoefQbarFiniteOmegaStageCoherence`. Updated the item's node to match
this proof. No existing module besides the assigned item is changed.

Validation: the assigned module compiled cleanly through `lcompile.py` in
45.7 seconds. The new finite omega module compiled in 2.1 seconds, with its one
explicitly recorded theorem hole.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CoefQbarVerdier.descendedEvaluation_equations`.
There are zero holes left in the assigned module.

Added one hole:
`WeilConjectures.CoefQbarVerdier.finiteOmegaStageComparison_tower`, in
`Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence`, node
`lem-coef-qbar-finite-omega-stage-coherence`.

This is a decomposition: one upper hole closed, one strictly smaller finite-stage
hole added, net zero holes closed. The remaining statement concerns only the
normalized finite omega maps and their associator; it has no descended object,
no descended dual, no evaluation, and no `FiniteCoherent` hypothesis. The full
categorical descent and evaluation argument is proved in the assigned module.

## No longer needed

No original import is removed, and no module is claimed globally prunable.
The direct proof-dependency edges to `lem-coef-integral-finite-extension`,
`def-weil-derived-pullback-tensor-hom`, and `thm-coef-rational-verdier` are replaced
by the precise finite omega, tensor inclusion, and finite evaluation statements.
Their mathematics remains transitively needed by those statements; this is not
a claim that the corresponding source-library declarations can be withdrawn.
The original coefficient-stage and representative-functor dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The original plan did not isolate the normalized finite omega tower equation in
the actual recorded stage system. The available finite evaluation and tensor
coherence declarations handle the other scalar squares, but they do not supply
that omega equation. The remaining work is to identify the localized integral
u-composition equation with the prescribed rational and recorded stage
associators. Its source and complete proof plan are in the new theorem's
docstring and node. No target statement or existing definition was changed,
and no statement is disputed.

## New nodes

`lem-coef-qbar-finite-omega-stage-coherence` states the tower equation for the
actual finite dualizing comparisons. Its module constructs the comparison from
`operationStageTransitionIso` and `F.scalar.omega`; only the tower proof is
postponed. The integral u-composition equation, rational scalar normalization,
and recorded transition/associator equalities give its proof. Identity
inclusions, repeated coefficient fields, zero objects, and the empty scheme
require no extra hypothesis. There are no change records because existing
statements and definitions are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence": "d2120d20eab649f1133f2f4c6fb8f79648d14b44", "Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent": "43c9b073c56040561e93084e4d38ac7249b74657"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierCore": {"hash": "9e958454f1e189dec671106840380e92f3724fdc", "status": "OK"}}, "seconds": 47, "time": "2026-10-28T06:55:19+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
