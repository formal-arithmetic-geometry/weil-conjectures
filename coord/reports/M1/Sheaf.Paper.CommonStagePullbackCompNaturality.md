## What changed

Filled the existing object and component declarations and proved the outer
naturality theorem by induction on `StageSystem.PairCategory.hom_induction`.
The representative-stage calculation is isolated as
`commonStagePullbackCompComponent_naturality_ofHom`; its proof remains a named
stage-3 split for the finite-stage scalar/compositor calculation.  Local
irreducibility annotations keep the component equality check within the compile
limit.

## Proved and sorry left

Proved `commonStagePullbackIntegralObject`,
`commonStagePullbackCompComponent_heq`, and
`commonStagePullbackCompComponent_naturality`.
The remaining sorry is
`commonStagePullbackCompComponent_naturality_ofHom`, recorded by node
`lem-zl-common-stage-pullback-comp-naturality-representative`; it is the
strictly smaller explicit-representative case used by the induction.

## No longer needed

No proof-dependency imports were removed. The exploratory local map helper was
removed because the final induction only invokes the representative theorem.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan omitted the explicit representative-stage
subproblem required to transport the integral compositor through the normalized
coefficient transitions. That subproblem is now stated as a separate node.

## New nodes

`lem-zl-common-stage-pullback-comp-naturality-representative` records the
finite-stage representative naturality calculation and is attached to
`commonStagePullbackCompComponent_naturality_ofHom` in the item module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonStagePullbackCompNaturality": "cccce65edb0d8fb71b21f229a7dbacc0830721de"}, "results": {"Sheaf.Paper.WeilIndSheafCategory": {"hash": "bf4aeb17d7fdb1b7ea0f2d376de5ea9d61745a37", "status": "OK"}}, "seconds": 57, "time": "2026-10-28T07:30:15+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
