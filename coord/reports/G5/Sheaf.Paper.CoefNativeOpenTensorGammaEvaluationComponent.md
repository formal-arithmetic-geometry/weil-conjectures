## What changed

Replaced the hole in
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensorGammaEvaluation_component`
by a categorical reduction to evaluation compatibility of restriction and tensor.
The original theorem statement is unchanged.

The proof identifies the two presentations of the derived exact adjunction:
localization of the termwise adjunction, and the right-derived adjunction
transported to the exact right functor. It compares their units on cochain
representatives and uses localization faithfulness. This justifies using the
unit and counit mate equations for the actual native `evalJ`.

A proved generic projection-square argument then uses `gamma_inverse` for the
system and finite models. Tensor naturality and the restriction square identify
their adjuncts; the counit equation identifies the inverse gamma composites;
cancellation yields the forward equation in the assigned theorem. The argument
is adapted from the proved private categorical lemma in
`Sheaf.SixFunctors.OpenTensorReductionSquare`, without importing that module's
unneeded geometric construction dependencies.

Added proof imports of the right-derived adjunction API, Mathlib adjunction
mates, and `Sheaf.Paper.CoefNativeRestrictionTensorEvaluation`. Added that last
module with the restriction/tensor evaluation substep, its source, its complete
proof in words, and its DAG node. Updated the assigned node's proof route.
All existing public signatures, definitions and imports remain unchanged.

The specialization supplies the native exact-functor instances explicitly.
Its final tactic constructs an ordinary application of the proved generic
lemma from the already elaborated model parameters; the kernel checks the
resulting proof in full. This follows the optimization already used by
`coefficientEvaluationTensorIso_exists` in the source calculus data.
The repeated model projections are handled inside a generic lemma, avoiding
repeated elaboration of the large native coefficient types. Both transparency
options are true; no heartbeat or compile-time limit is raised.

## Proved and sorry left

Closed the original syntactic hole in
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensorGammaEvaluation_component`
(node `lem-coef-native-open-tensor-gamma-evaluation-component`) by a complete
Lean combination of the restriction square, adjunction mate equations, the
model fields, and categorical naturality/cancellation.

Added one hole:
`WeilConjectures.CoefSupportOpenTensor.nativeRestrictionTensorEvaluation`
(node `lem-coef-native-restriction-tensor-evaluation`). Its proof body is exactly
`by sorry`. It concerns two ambient derived objects and restriction/tensor only;
it does not assert gamma evaluation or contain any extension-by-zero comparison.
The removed work comprises identification of the derived adjunctions and the
entire passage from the restriction square to the open projection formula.
Thus this delivery is a decomposition: one upper hole closed, one strictly
smaller hole added, net zero holes. The item module has zero remaining holes;
the delivery has one remaining hole, in the new module. Every private helper is
proved.

Validation: both modules compiled in dependency order through `lcompile.py`
(the item took 19.5 seconds in the diagnostic run). Diagnostic and trace options
were removed afterwards. The delivery tool records the final clean compile,
axiom probes and preflight checks. The proof preserves all object and
coefficient-degree binders.

## No longer needed

The assigned node's previous direct proof dependencies
`lem-coef-derived-system-evaluation-calculus`,
`lem-weil-pbc-ringed-topos-kflat-pullback`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-sf-ringed-slice-tensor-generators` are replaced by the restriction-square
node, exact-derived adjunction data, native varying-ring operations, and open
model representative data. The assigned proof performs no generator or K-flat
descent calculation itself. Evaluation calculus is still used by the new
restriction-square step; the representative descent route is the existing
four-model argument of `GeometricTensorEvaluation`.

In particular, the ringed-slice tensor-generator detour is not required for
this evaluation argument: the open models already contain their restriction
normalizations. No existing module is withdrawn, and no original public import
is removed. No claim is made that the old dependency modules are globally unused.

## Where the brief, the DAG or earlier work was wrong

The old node's generator/descent plan mixed the restriction/tensor square with
the open-extension projection formula. Its statement dependencies supply the
`gamma_inverse` equations already, so the open-extension part is a categorical
mate calculation. This delivery proves that part instead of splitting the same
pointwise gamma equation under another name.

The exact adjunction used by `OpenTensorModel` and the right-derived adjunction
used to define native `evalJ` have different constructions. Their equality must
be proved, rather than treating their units as definitionally identical.
The generic localization argument in this delivery supplies that identification.

The restriction square passes edge checks for the identity and empty open,
zero objects and n = 0. All are covered by the same adjunction unit and
pure-tensor normalizations; no nonzero-object, nonempty-open, or positive-degree
hypothesis has been added. The unit route is unchanged.

## New nodes

`lem-coef-native-restriction-tensor-evaluation` records compatibility of exact
finite evaluation with the normalized inverse-image tensor comparison. It is
strictly the restriction/tensor portion of the original generator calculation.
Blueprint searches for “tensor evaluation” and “restriction tensor” found no
matching blueprint statement (the former found only `lem-fix-weil-operations`).
Its two steps give the ordinary pure-tensor/unit argument and the total-complex
and resolving-representative descent. The module is
`Sheaf.Paper.CoefNativeRestrictionTensorEvaluation`. No change record is needed:
no other existing module or node is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefNativeOpenTensorGammaEvaluationComponent": "04cb9de6544ff3c92cedbe47b0baf07692c849b3", "Sheaf.Paper.CoefNativeRestrictionTensorEvaluation": "7626e41db1f79703c60b64b3e9c2f26b861364f9"}, "results": {"Sheaf.Paper.CoefNativeOpenTensorGammaEvaluation": {"hash": "6a02524c6e05f407537fff99d309a5abd3644b0e", "status": "OK"}}, "seconds": 28, "time": "2026-10-28T03:39:49+0800", "transitive": 0, "version": 1}
```

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
