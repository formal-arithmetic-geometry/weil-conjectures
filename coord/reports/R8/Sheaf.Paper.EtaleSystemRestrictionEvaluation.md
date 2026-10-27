## What changed

Rebased the assigned module onto the current source and verified that its target theorem compiles in the R8 sandbox. The theorem statement and imports remain unchanged.

## Proved and sorry left

No holes were closed. The theorem `AlgebraicGeometry.Etale.SystemProjection.etaleSystemRestriction_evaluation` remains one `sorry` (node `lem-pur-etale-system-restriction-evaluation`).

## No longer needed

No imports, nodes, or modules were pruned from the assigned module.

## Where the brief, the DAG or earlier work was wrong

A prior decomposition from another group depended on helper modules whose current source did not compile within the per-file limit; those helper files were not included in this delivery. The current global build also has an unrelated failure in `Sheaf.Paper.IntegralProperReductionBound`, recorded in the build-error file.

## New nodes

None.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleSystemRestrictionEvaluation": "0e35cb4a4e677ae5add2918a4b2f9f89d99e911b"}, "results": {}, "time": "2026-10-28T01:11:46+0800", "transitive": 0, "version": 1}
```

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
