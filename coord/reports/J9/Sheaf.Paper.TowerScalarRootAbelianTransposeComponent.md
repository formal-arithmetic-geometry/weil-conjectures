## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.scalarRoot_abelianTranspose_component` by expanding both adjunction transposes to their unit formulas, applying the supplied section identity for `χ`, and composing the resulting heterogeneous equality with a new χ-free finite-level core theorem. Added `Sheaf.Paper.TowerScalarRootAbelianTransposeCore`, including the explicit source and target finite-level values.

## Proved and sorry left

- Proved `scalarRoot_abelianTranspose_component` (1 of 1 original sorry closed).
- Added `scalarRoot_abelianTranspose_core`, with one `sorry` remaining for the χ-free root normalization comparison.

## No longer needed

None. Both original public imports are needed for the statement, and the proof uses the restricted scalar adjunction and class pullback declarations. The new core module uses the same two imports.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan omitted the intermediate χ-free comparison needed after unfolding the two adjunction units. The assigned component theorem is proved from that strictly smaller finite-level statement; no target signature was changed.

## New nodes

- `lem-sp-tower-scalar-root-abelian-transpose-component-core` (copied as `dag/nodes/sec-smooth-purity/lem-sp-tower-scalar-root-abelian-transpose-component-core.json`).

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TowerScalarRootAbelianTransposeComponent": "0332fa4934e6d0e2c2b5d90bddd1eee9f710ace3", "Sheaf.Paper.TowerScalarRootAbelianTransposeCore": "ae26bbab61b86dc1e91a8466c4e1a733cd282e03"}, "results": {}, "time": "2026-10-28T05:36:24+0800", "transitive": 0, "version": 1}
```

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
