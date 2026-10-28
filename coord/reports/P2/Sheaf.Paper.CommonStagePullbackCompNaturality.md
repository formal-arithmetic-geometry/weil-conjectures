## What changed

Moved the common-stage component construction into `Sheaf.Paper.CommonStagePullbackCompComponent` and added finite-stage auxiliary statements for its representation, rational naturality, and conjugated square. The representative naturality theorem now combines the recorded pullback map representations with these finite-stage statements and a real `ofHom` composition calculation. The final all-morphisms naturality theorem remains obtained by pair-category hom induction.

## Proved and sorry left

Closed the original `commonStagePullbackCompComponent_naturality_ofHom` sorry. Split off five finite-stage statements. Proved (reviewer fix): `commonStageDerivedPullback_object_representation` and `commonStageDerivedPullback_map_representation` (the two clauses of `commonStageDerivedPullback_existsUnique`), and `commonStagePullbackCompComponent_stage_square` (cancellation plus rational naturality). Left with `sorry`: `commonStagePullbackRationalComposition_naturality` and `commonStagePullbackCompComponent_stage_representation`.

## No longer needed

`lem-pod-pullback-identities-scalar-extension` is no longer used directly by the proof of `commonStagePullbackCompComponent_naturality_ofHom`; it is used by `lem-zl-common-stage-pullback-comp-stage-representation`. (The representative node lem-zl-common-stage-pullback-comp-naturality-representative is not a file of this delivery, so its proof_deps still name the old plan. They should name the object, map and stage representation nodes and the stage-square node.) The direct proof uses the component construction, the common-stage pullback map specifications, and the finite-stage compositor statements.

## Where the brief, the DAG or earlier work was wrong

The original module combined the component definition and its naturality proof, while the finite-stage transport facts were not separately declared. They are now explicit lower statements so the parent proof has a concrete Lean reduction.

## New nodes

Added finite-stage auxiliary nodes `lem-zl-common-stage-pullback-comp-rational-naturality`, `lem-zl-common-stage-pullback-comp-stage-representation`, `lem-zl-common-stage-pullback-comp-stage-square`, `lem-zl-common-stage-pullback-comp-object-representation`, and `lem-zl-common-stage-pullback-comp-map-representation`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonStagePullbackCompComponent": "f3b7f3a949611a184339f21803253f56f2ad7344", "Sheaf.Paper.CommonStagePullbackCompNaturality": "f15c02b28564d3ccfeb1d698e3f07c67edfbf434"}, "results": {"Sheaf.Paper.WeilIndSheafCategory": {"hash": "bf4aeb17d7fdb1b7ea0f2d376de5ea9d61745a37", "status": "SLOW"}}, "seconds": 122, "time": "2026-10-28T09:33:07+0800", "transitive": 0, "version": 1}
```

## Reviewer correction

The reviewer proved three of the five split statements, gave the new nodes real statements and owner stmt_deps, and recorded `commonStagePullbackRationalComposition` in the rational-naturality node. The representative node is outside the files of this delivery and was not changed.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
