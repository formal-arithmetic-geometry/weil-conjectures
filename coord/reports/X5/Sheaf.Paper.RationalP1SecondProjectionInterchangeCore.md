## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.secondTraceStrength_naturality`.
The proof expands the shifted strength and tail, uses the public tensor-shift
naturality theorem, cancels the pullback tensorator with its inverse, and closes
the remaining associator/braiding coherence by private generic categorical
lemmas. Added the proof-only import of
`Sheaf.Paper.RationalP1TensorShiftNaturality` and updated the item node's proof
route to record that dependency.

## Proved and sorry left

The item theorem `secondTraceStrength_naturality` is proved. The module has zero
remaining `sorry`s and the delivery adds none.

## No longer needed

No imports or nodes were removed. The proof uses both original definition
dependencies and `lem-sfb-rational-p1-tensor-shift-naturality`; all planned
projection-tail dependencies remain outside this generic core.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the already stated tensor-shift naturality
lemma from `proof_deps`; the node copy now records it. No statement or
mathematical route is disputed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SecondProjectionInterchangeCore": "2a6d33a656f257ab1458dfba2491dd4874cfdebc"}, "results": {"Sheaf.Paper.RationalP1SecondProjectionInterchange": {"hash": "4e32217ceb9ceb3840280046d74161f1ddb8e93e", "status": "INFRA"}, "Sheaf.Paper.RationalP1SecondProjectionInterchangeTail": {"hash": "ec81c76f4331a813773e544e5a3c2242c3ee0995", "status": "OK"}}, "seconds": 116, "time": "2026-10-28T08:40:38+0800", "transitive": 0, "version": 1}
```

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
