## What changed

The assigned module now imports two proof-only helper modules and combines their results. `lisseTower_localized_actual_levels` supplies the family of level isomorphisms, while `lisseTower_localized_actual_normalized` supplies the transition equation for any such family. Both helpers are documented split-off statements with matching DAG nodes.

## Proved and sorry left

The assigned theorem `AlgebraicGeometry.Scheme.lisseTower_localized_actual` is proved by constructing the level family and applying the normalized-transition theorem. The two split-off helper declarations `AlgebraicGeometry.Scheme.lisseTower_localized_actual_levels` and `AlgebraicGeometry.Scheme.lisseTower_localized_actual_normalized` remain `sorry`, each with its own node; this is a decomposition into the two independent mathematical steps.

## No longer needed

The assigned module no longer directly uses the original proof-dependency declarations; those dependencies are retained by the split-off helper nodes where their respective constructions are stated. No public import was removed. No unrelated module or node was pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled level construction and transition coherence into one theorem. The Lean statement naturally separates them: the level family does not require the scalar-square or descent-equation inputs, while the normalized equation takes a previously constructed family as input. The route was therefore decomposed into these two strictly simpler statements.

## New nodes

`lem-weil-pbc-lisse-tower-localized-actual-levels` records the level-comparison construction and is stated in `Sheaf.Paper.LisseTowerLocalizedActualLevels`.

`lem-weil-pbc-lisse-tower-localized-actual-normalized` records the normalized transition equation and is stated in `Sheaf.Paper.LisseTowerLocalizedActualNormalized`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.LisseTowerLocalizedActual": "9c56cf135ee8029e80efee23a8c4843c97c397aa", "Sheaf.Paper.LisseTowerLocalizedActualLevels": "1497c5c207da7b166a9f5d83c9096936251270ef", "Sheaf.Paper.LisseTowerLocalizedActualNormalized": "f83980edb57edcda671abf38c15af70f7da7ef2c"}, "results": {}, "time": "2026-10-28T08:00:13+0800", "transitive": 0, "version": 1}
```

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
