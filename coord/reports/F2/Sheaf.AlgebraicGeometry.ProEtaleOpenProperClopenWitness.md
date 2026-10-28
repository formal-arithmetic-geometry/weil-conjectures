## What changed

Filled the sole proof hole in `Sheaf.AlgebraicGeometry.ProEtaleOpenProperClopenWitness`.
The proof takes `V := B ×_D E`, uses its projections and the canonical pullback lift of
`k` and `r`, and packages the pullback equations into `OpenProperClopenWitness`.  The
existing `AlgebraicGeometry.ProEtale.StrictTower.squareLift_clopen` theorem supplies the
open and closed immersion properties of the lift.  Added the proof-only import
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`; no public signature or definition
changed.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.exists_openProperClopenWitness` (1 of 1 sorries).
The delivered item has zero remaining sorries and adds no sorries.

## No longer needed

No modules are withdrawn.  The original planned direct dependencies on separate
open-immersion base-change, proper base-change, proper-over-separated, and
proper-immersion-closed nodes are not imported directly: their geometric conclusion is
provided by the existing strict-tower `squareLift_clopen` declaration.  The retained
proof dependencies are `def-pc-fibre-product` and
`def-cbc-strict-tower-proper-open-arrows`.  The direct importer
`Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicFromWitness` was compiled
unchanged against the delivered module.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan described the fibre-product construction but listed several
lower geometric lemmas individually.  The library already contains their assembled
strict-tower theorem, so the proof can use that strictly shorter route while preserving
the unit's geometric factorisation.  No statement is changed or disputed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleOpenProperClopenWitness": "9485d06721f11d3ba856891fa12abd28a58fefcb"}, "results": {"Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclicFromWitness": {"hash": "8d216ad4c5c7ec7026d145f2d611ab2ac11c6a25", "status": "OK"}}, "seconds": 6, "time": "2026-10-28T09:25:55+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
