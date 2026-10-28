## What changed

Proved `WeilConjectures.CoefQbarVerdier.finiteOmegaStageComparison_tower`.
The module now imports two proof-only modules containing the strictly simpler
rational omega transition tower and operation-stage transition tower statements.
A private categorical transport lemma combines their equations with naturality of
`operationStageTransitionIso`.

## Proved and sorry left

The item theorem `finiteOmegaStageComparison_tower` is proved. Two strictly simpler
supporting statements are split off and remain as named `sorry`s:

- `WeilConjectures.CoefQbarVerdier.finiteOmegaTransition_tower`
  (`lem-coef-qbar-finite-omega-transition-tower`)
- `WeilConjectures.CoefQbarVerdier.operationStageTransitionIso_tower`
  (`lem-coef-qbar-operation-stage-transition-tower`)

## No longer needed

The item's proof no longer imports the broad integral composition and rational scalar
composition modules from the original DAG plan directly. Their consequences are
encapsulated by the two split-off tower statements. No existing proof dependency
module is removed from the library.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the categorical transport step that combines the
naturality square, stage-system associator transport, and finite omega tower equation.
The missing step is now a proved generic private lemma. The two remaining holes are
strictly simpler component equations rather than a restatement of the item theorem.

## New nodes

Added `lem-coef-qbar-finite-omega-transition-tower`, recording the localized rational
omega composition equation, and `lem-coef-qbar-operation-stage-transition-tower`,
recording transport of the stage-system associator through the operation transition
isomorphisms.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence": "94ed9853fdc6ad1f972f690bbbe5115339c9a699", "Sheaf.SixFunctors.CoefQbarFiniteOmegaTransitionTower": "6513e73287bf8a6af5cb86ac7545302610a0d0ce", "Sheaf.SixFunctors.CoefQbarOperationStageTransitionTower": "3bd42886eadf74fce10f647a75a20e49819cbe06"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent": {"hash": "43c9b073c56040561e93084e4d38ac7249b74657", "status": "OK"}}, "seconds": 69, "time": "2026-10-28T09:45:53+0800", "transitive": 0, "version": 1}
```

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
