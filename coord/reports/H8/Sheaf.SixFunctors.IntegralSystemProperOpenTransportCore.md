## What changed

Added two proof-dependency modules splitting the transport argument into the adjunct-normalized gamma package and its canonical bridge equation. The item module now imports the canonical module and combines the two intermediate results into `ProperOpenTransportCore`.

## Proved and sorry left

The item theorem `integralSystemProperOpenTransportCore` is proved by combining the two named intermediate theorems. Two strictly simpler intermediate theorem statements remain sorry: `integralSystemProperOpenTransportAdjunct` and `integralSystemProperOpenTransportCanonical`, with nodes `lem-sf-integral-system-proper-open-transport-core-adjunct` and `lem-sf-integral-system-proper-open-transport-core-canonical`.

## No longer needed

The attempted direct bridge-conjugation term was removed; no additional proof imports beyond the canonical intermediate module are needed by the item.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan did not provide declarations exposing the bridge-conjugation and cancellation arguments, and direct elaboration exceeded the heartbeat limit. The proof was therefore split into the two genuine mathematical components described by the source proof.

## New nodes

`lem-sf-integral-system-proper-open-transport-core-adjunct` records existence of the transported gamma with the normalized adjunct law. `lem-sf-integral-system-proper-open-transport-core-canonical` records the canonical bridge equation for that adjunct-normalized gamma.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemProperOpenTransportAdjunct": "204ea3d40d316d8719b03fdcb7cf062518e33ed8", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportCanonical": "f248118d8fe44ea92aed6b69e0329d390636cde7", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportCore": "6d57fb6c3fb6c1951ca387f5a172981d77ae77db"}, "results": {}, "time": "2026-10-28T03:58:38+0800", "transitive": 0, "version": 1}
```

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
