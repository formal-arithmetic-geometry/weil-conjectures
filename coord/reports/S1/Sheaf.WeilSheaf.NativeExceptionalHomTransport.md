## What changed

Updated `lean/Sheaf/WeilSheaf/NativeExceptionalHomTransport.lean` by decomposing the theorem into three named component statements and proving the original conjunction from them. The component proofs remain explicit staged obligations with source-based proof plans.

## Proved and sorry left

The original `counitHomTransport_compatible` theorem is proved by combining the three component declarations. Three component sorries remain: `counitHomTransport_action_compatible`, `counitHomTransport_forget_compatible`, and `counitHomTransport_boundary_compatible`, with nodes `lem-sf-native-exceptional-hom-transport-action`, `lem-sf-native-exceptional-hom-transport-forget`, and `lem-sf-native-exceptional-hom-transport-boundary`.

## No longer needed

The proof body no longer directly imports `Sheaf.CategoryTheory.CyclicDerivedHomExactSequence` or `Sheaf.CategoryTheory.ExactInputDerivedTransformation`; these imports were removed from the item while the split component nodes retain them as proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The assigned theorem requires assembling exact-open and total-right-derived transports through `CyclicDerivedTransport.Generated`; direct elaboration of that assembly exceeded the single-file heartbeat/time budget before the component projections could be applied. The three split statements are strict components of the conjunction and preserve the stated route.

## New nodes

Created `lem-sf-native-exceptional-hom-transport-action`, `lem-sf-native-exceptional-hom-transport-forget`, and `lem-sf-native-exceptional-hom-transport-boundary`, each a strict component of the parent transport theorem with the exact open/proper finite-composite proof plan.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalHomTransport": "60769bba245635fc0e31e94d24d7b87dd90d8740"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounit": {"hash": "38d8da350553c21ab8acf4601f5ef60e14e4c474", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness": {"hash": "6d9ff825e9bb3fda66d8f1af50c3c594981792d5", "status": "OK"}}, "seconds": 16, "time": "2026-10-28T07:37:06+0800", "transitive": 0, "version": 1}
```

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
