## What changed

Repaired `Sheaf.Paper.CompactSupportNormalizedScalarDescent` by proving its conjunction from two named component theorems. Added unit and tower component modules and DAG nodes; each component retains the corresponding unresolved whole-system argument as a named theorem with `sorry`.

## Proved and sorry left

Closed `WeilConjectures.sfCompactSupportNormalizedScalarDescent` (1 of 1 original sorries) by a genuine conjunction proof. Added `WeilConjectures.sfCompactSupportNormalizedScalarDescentUnit` and `WeilConjectures.sfCompactSupportNormalizedScalarDescentTower`, each with one `sorry` for the strictly smaller component calculation.

## No longer needed

None. The parent module's existing imports remain required by the component signatures and declarations.

## Where the brief, the DAG or earlier work was wrong

The prior global build failure was caused by stale missing imports in the quarantined snapshot. The source itself compiles once the current dependency modules are present. The original proof is too large to close directly within this item, so it is decomposed into the unit and tower equations explicitly.

## New nodes

- `lem-weil-compact-support-normalized-scalar-descent-unit`
- `lem-weil-compact-support-normalized-scalar-descent-tower`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportNormalizedScalarDescent": "6c7c25fb0eb44a4633534e59d0bfe31c66f7496e", "Sheaf.Paper.CompactSupportNormalizedScalarDescentTower": "05d7f1c1e7639986cebd67503ba00ab67ab3d425", "Sheaf.Paper.CompactSupportNormalizedScalarDescentUnit": "1bd7a8aabdf4843146cf1a902b75f4a3de8a57bd"}, "results": {}, "time": "2026-10-28T01:18:20+0800", "transitive": 0, "version": 1}
```

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
