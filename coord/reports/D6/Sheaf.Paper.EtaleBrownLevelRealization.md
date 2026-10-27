## What changed

Split the realization existence proof into two named intermediate theorems. Added `EtaleBrownLevelRealizationData.lean` for existence of the realization data and `EtaleBrownLevelRealizationCoherence.lean` for its coherence equations. The item module now combines these two statements in a complete Lean proof.

## Proved and sorry left

`AlgebraicGeometry.etaleBrownLevelRealization_exists` is proved from the two intermediate declarations. Two strictly simpler proof obligations remain as named `sorry` theorems: `etaleBrownLevelRealizationData_exists` and `etaleBrownLevelRealizationCoherence_exists`.

## No longer needed

Removed the exploratory proof import `Sheaf.CategoryTheory.ConstantRingModuleSheaves`; the final reduction does not use it. The item still uses the projection realization interface and the two split modules.

## Where the brief, the DAG or earlier work was wrong

The original node bundled construction of all realization data with three independent normalization equations. The available interface does not provide a single theorem for that bundle, so the proof was decomposed into the data and coherence obligations, which are strictly smaller and correspond to the two stages of the written argument.

## New nodes

Added `lem-pur-etale-brown-level-realization-data` for `AlgebraicGeometry.etaleBrownLevelRealizationData_exists` and `lem-pur-etale-brown-level-realization-coherence` for `AlgebraicGeometry.etaleBrownLevelRealizationCoherence_exists`. Their node files are in `dag/nodes/sec-smooth-purity/`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleBrownLevelRealization": "bd3c3eb089f60c63fef3b7104ac08e9a21362645", "Sheaf.Paper.EtaleBrownLevelRealizationCoherence": "b98fbc1ff82645d5b08f6a27b343e001fb589492", "Sheaf.Paper.EtaleBrownLevelRealizationData": "3581a5b31d0059d275eb8f2fcb2cce75ae6bbf5f"}, "results": {}, "time": "2026-10-28T03:42:26+0800", "transitive": 0, "version": 1}
```

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
