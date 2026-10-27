## What changed

Restored `lean/Sheaf/Paper/IntegralDirectImageTowerData.lean` from its quarantined
source. In `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Evaluation.derived`,
changed the existing `hAdd` binding from `let` to `letI`. The proved additivity of
finite coefficient evaluation is now available to instance inference throughout
the composite derived comparison. The explicit `hAdd` argument is retained.
All public declarations, signatures, imports, constructions and normalizations
are preserved. No other existing module or node changes.

Validation: the repaired module compiled in 41.3 seconds with exit code 0.
All six direct importers compiled individually in import order against the sandbox
overlay, with exit code 0 and no compiler errors or warnings. These unchanged
consumer copies were then removed. The delivered Lean file has no `sorry`, no
forbidden declarations and no lines over 100 characters.

Change record: `coord/changes/B4-integral-derived-evaluation-local-instance.md`.

## Proved and sorry left

This is the assigned zero-hole definition repair. Original holes: 0; holes
closed: 0; holes added: 0; holes remaining in the delivered module: 0. No
statements are split off. The node is `def-sp-integral-direct-image-tower-data`.

## No longer needed

None. No imports, nodes, modules or declarations are removed or bypassed. The
existing statement dependencies and unit route remain intact.

## Where the brief, the DAG or earlier work was wrong

The recorded global-build failure is an elaboration defect, not an unfinished
mathematical proof: the proof of additivity was present but was not registered
as a local instance. Current queue, rework, build-error, claim and return records
were checked on the server before repairing the preserved quarantined source.
Searches with Loogle, LeanFinder and grep confirmed the existing generic exact
functor API and additivity theorem used by this construction; no replacement
construction or additional dependency is needed.

## Related modules compiled before delivery

6 related module(s) compiled against this delivery by deliver3.py: 6 OK.

```json
{"capped": false, "direct": 6, "left_out": 0, "own": {"Sheaf.Paper.IntegralDirectImageTowerData": "5ef02a3a77ee4a8174e28b2f47db1b617c10bf19"}, "results": {"Sheaf.Paper.IntegralDirectImageTower": {"hash": "17ff89ebf89e1a75370a170349d007811858cc9f", "status": "OK"}, "Sheaf.Paper.IntegralTowerCompactificationCoherence": {"hash": "856452eebe79bc6295da0a836209b1feafd54273", "status": "OK"}, "Sheaf.Paper.IntegralTowerGeometryLimits": {"hash": "3406bfe6b1c036874ea3bca6b1c01c10b0443f38", "status": "OK"}, "Sheaf.Paper.IntegralTowerImageReconstruction": {"hash": "ac50f45fa9b0dd6d1a661f168ba6af998291308d", "status": "OK"}, "Sheaf.Paper.IntegralTowerProjectionMates": {"hash": "7a685f1626707855945b08c3c7146271f5d93b75", "status": "OK"}, "Sheaf.Paper.IntegralTowerPullTensorConstructible": {"hash": "86d46eb09ff40f9fee0fa6a87fce44dba1c2cc4f", "status": "OK"}}, "seconds": 121, "time": "2026-10-28T02:53:02+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
