## What changed

Restored and proved the categorical assembly for `Sheaf.Paper.ConstructibleCompactSupportTargetIso`. Added `ConstructibleCompactSupportTargetIsoStage.lean`, which states the remaining geometric common-stage comparison, and `ConstructibleCompactSupportTargetIsoDescent.lean`, which proves descent of coherent stage isomorphisms to the pair-category functors. The target theorem now obtains the stage comparison and applies the proved descent construction.

## Proved and sorry left

Closed the target theorem `constructible_compact_support_target_iso` by reducing it to the two named components. Proved `stageSystem_iso_of_restrictions` with no `sorry`. Added one strictly simpler split-off theorem, `constructible_compact_support_target_stage_comparison`, whose proof remains `sorry` and is the finite/common-stage geometric comparison required by the target.

## No longer needed

The original seven proof dependencies of the target are no longer imported by the target module's proof route; they are summarized by the split-off stage comparison theorem. No existing library modules were removed.

## Where the brief, the DAG or earlier work was wrong

The inherited proof plan bundled finite geometric comparison, coefficient descent, and pair-category naturality into one unsplit obligation. The delivery separates the categorical descent, which is elementary and fully proved, from the genuinely geometric stagewise comparison. The target statement and all hypotheses are unchanged.

## New nodes

`lem-sf-constructible-compact-support-target-stage-comparison` records the remaining finite/common-stage geometric comparison and its source route.

`lem-sf-constructible-compact-support-target-stage-descent` records the proved directed-stage categorical assembly.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstructibleCompactSupportTargetIso": "f16d0d15f1ad9f5bd295e86c5c590d90e52a37f3", "Sheaf.Paper.ConstructibleCompactSupportTargetIsoDescent": "1ec8448096fed3feab660be141752c244719ef11", "Sheaf.Paper.ConstructibleCompactSupportTargetIsoStage": "0b353924823e7e050bebbe914f337cc718bea5a6"}, "results": {}, "time": "2026-10-28T01:23:33+0800", "transitive": 0, "version": 1}
```

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
