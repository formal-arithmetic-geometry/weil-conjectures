## What changed

Restored the assigned module from quarantine and repaired its historical missing-import state. The parent cochain-map proof is now a genuine homological-complex extensionality argument from a strictly smaller sectionwise projection theorem. Added `Sheaf.SixFunctors.PullQuotientOrdinaryProjectionSection` for that sectionwise theorem.

## Proved and sorry left

The parent declaration `pullQuotientOrdinaryProjection` is proved. One strictly smaller theorem remains sorry: `pullQuotientOrdinaryProjection_section`.

## No longer needed

No imports were removed. The parent proof uses only the new sectionwise theorem and the definitions already present in `IntegralSystemCanonicalBridge`; no additional planned proof dependency was needed beyond those named in the node.

## Where the brief, the DAG or earlier work was wrong

The quarantined source imported `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`, which is present in the current tree; the historical build error recorded a stale bad-import snapshot. The original proof plan was too coarse for direct automation, so the sectionwise calculation was split off as a strictly simpler statement and the chain-map assembly was proved explicitly.

## New nodes

`lem-sf-pull-quotient-ordinary-projection-section` — sectionwise finite projection identity, with its proof currently left as a named sorry.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.PullQuotientOrdinaryProjection": "52903377f72fbecdcf9a1fd608f6afa1373fc8da", "Sheaf.SixFunctors.PullQuotientOrdinaryProjectionSection": "169b5f4c7ec48ca91a0e1f75bcd50f175cd5eba5"}, "results": {}, "time": "2026-10-28T00:46:53+0800", "transitive": 0, "version": 1}
```

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
