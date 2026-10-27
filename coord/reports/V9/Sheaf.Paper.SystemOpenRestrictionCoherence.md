## What changed

Reduced `systemOpenRestrictionCoherence` to two strictly smaller named statements: construction of normalized open data and their derived cocycle/unit laws. Added and imported `SystemOpenRestrictionData` and `SystemOpenRestrictionLaws`.

## Proved and sorry left

`systemOpenRestrictionCoherence` is proved. `systemOpenRestrictionData` and `systemOpenRestrictionLaws` remain sorry as the two split-off nodes.

## No longer needed

Removed exploratory proof imports; no declared dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof step combined construction and coherence; this delivery separates the two strictly smaller obligations.

## New nodes

Added `lem-sp-system-open-restriction-data-existence` and `lem-sp-system-open-restriction-laws`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.SystemOpenRestrictionCoherence": "66f2e0a62494a0cec3183e6566d1dbb976a2ae70", "Sheaf.Paper.SystemOpenRestrictionData": "c9af7bc79525892d82bacbafc9f04b312727b7aa", "Sheaf.Paper.SystemOpenRestrictionLaws": "1f8390eb19f29c7acde7250fc24dc8423dfa2ab0"}, "results": {}, "time": "2026-10-28T01:19:25+0800", "transitive": 0, "version": 1}
```

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
