## What changed

Added the named finite-stage representative lemma
`commonStageDerivedPullback_map_inclusion`, isolating the common-stage map formula
needed by the rational-to-common transport. The original `commonUnit_frobenius`
hole remains open for a later worker; its statement and definitions are unchanged.

## Proved and sorry left

No existing holes were closed. `commonUnit_frobenius` remains `sorry`. The new
`commonStageDerivedPullback_map_inclusion` theorem is a strictly smaller
finite-stage transport statement and remains `sorry` for follow-up proof.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The rational coherence theorem does not directly typecheck at the common stage;
the finite-stage representative formula is an additional argument step.

## New nodes

`lem-pur-common-constant-unit-frobenius-transport` records the finite-stage map
formula used in the common-stage transport.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonConstantUnitFrobenius": "3e24bc10013089f3622934ae5565cdfaabe43f79"}, "results": {"Sheaf.Paper.ConstantPurityFrobeniusSquare": {"hash": "57e1afb9cc6da75a28f05ec3856b5b1c77ee5d7b", "status": "INFRA"}}, "seconds": 99, "time": "2026-10-28T08:12:29+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
