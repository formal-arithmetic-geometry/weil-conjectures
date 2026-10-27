## What changed

The target theorem in `lean/Sheaf/TraceFormula/ScalarModelRoosZeroLiftExistence.lean` is now proved by combining two strictly smaller interfaces. `ScalarModelRoosZeroLiftCore.lean` states the realization/transpose construction of the lift, its zero shifted coordinate, and its normalized quotient coordinates. `ScalarModelRoosZeroLiftFactorization.lean` states the remaining counit factorization from those data. The target imports both proof modules and combines their conclusions with `obtain`, tuple construction, and direct application.

## Proved and sorry left

The target declaration `WeilConjectures.scalarModelRoosZeroLift_existence` is proved (one sorry closed). Two strictly simpler intermediate declarations remain as named split-off obligations: `WeilConjectures.scalarModelRoosZeroLift_core` and `WeilConjectures.scalarModelRoosZeroLift_factorization` (two sorries added), each recorded by a new DAG node.

## No longer needed

No prior proof imports were removed. The original monolithic construction proof is replaced by the two interfaces above; no declared dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The existing node bundled the construction, coordinate normalization, and counit factorization into one statement. The available realization-model declarations expose these as separate mathematical stages, so the proof is decomposed into the construction-data and factorization nodes while preserving the target statement unchanged.

## New nodes

`lem-trf-scalar-model-roos-zero-lift-core` records the strict lift, zero-shift, and normalized-coordinate construction in `Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore`.

`lem-trf-scalar-model-roos-zero-lift-factorization` records the counit factorization from those construction data in `Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.ScalarModelRoosZeroLiftCore": "701f9778dd774a9b8d487df62d9f46ac184063c9", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftExistence": "ad3dab305234dd1c065828ea0c45c7c89324a5f0", "Sheaf.TraceFormula.ScalarModelRoosZeroLiftFactorization": "0c8e7fbdbbe1945ef3a238f25b70457b3358a968"}, "results": {}, "time": "2026-10-28T04:19:38+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
