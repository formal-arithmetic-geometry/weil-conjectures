## What changed

Restored the quarantined module source required by the rework assignment and repaired its
universe inference. The file now locally prioritizes `SheafOfModules.instAbelian` for
`integralTowerModules`, which fixes the `EssentiallySmall` universe constraint at the
coincident-boundary homology step. The previous explicit
`PointQuotientAugmentation.roosComparison` arguments in both scalar Roos isomorphism
proofs are retained. No public definition or theorem statement changed.

## Proved and sorry left

`WeilConjectures.trfBoundedQuotientStalkRealization` remains fully proved. The module has
zero `sorry` declarations before and after this repair, and the delivery adds no new holes.

## No longer needed

No imports, nodes, or modules were removed. All existing proof dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was removed by the red-build recovery because the imported module had
an ambiguous sheaf-of-modules abelian instance after downstream imports changed. The exact
failure was the universe constraint at line 311:
`u + 1 =?= max (u + 1) ?u`. Restoring the quarantine source and adding the documented local
instance priority resolves that constraint without changing the mathematical route or the
statement. The earlier scalar Roos explicitness repair is preserved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TraceBoundedQuotientStalkRealization": "4a08e0ccb8097b195b9ca2121b9248c8538f07f6"}, "results": {}, "time": "2026-10-28T06:06:33+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
