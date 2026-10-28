## What changed

Restored the three public pullback composition declarations to their original
item module and removed the unforced relocation module. The former witness-only
split was withdrawn. The new split-off module states a strictly smaller
transition naturality fact for the normalized compositor and proves it by
specializing the existing common-stage compositor naturality theorem. The
composition existence theorem remains available for the next proof step and is
not discharged merely by naming its witness.

## Proved and sorry left

Closed: none of the original six holes.

Split off one strictly smaller theorem:
`WeilConjectures.commonStagePullbackCompComponent_transition`.

The six original holes remain, including
`WeilConjectures.pullbackTensorCommonComposition_exists`; its witness-only proof
was removed. The other five are unchanged:

- `WeilConjectures.pullbackTensorCommonAssociator_exists`
- `WeilConjectures.pullbackTensorCommonBraiding_exists`
- `WeilConjectures.pullbackTensorRationalScalarUnit_existsUnique`
- `WeilConjectures.pullbackTensorCommonLeftUnitor_existsUnique`
- `WeilConjectures.pullbackTensorCommonRightUnitor_existsUnique`

## No longer needed

The relocated `PullbackTensorCompositionDefinitions` module and its node were
removed. The original declarations remain in their owner module, preserving the
existing ownership and public interface. The prior witness-only representative
module and node were also withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery treated the full representative identity as an admitted
helper and then selected its witness, which did not prove any part of the item.
The repaired delivery splits only the stage-transition naturality substep; this
is strictly smaller because it contains no compositor formula, scalar
cancellation, or integral/rational identification.

## New nodes

`lem-h3-common-stage-pullback-composition-transition` records the smaller
transition naturality substep and its proof dependency.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CommonStagePullbackCompositionTransition": "323ae60cebd2d3e36aea49d66034668e6937ebb1", "Sheaf.Paper.DerivedPullbackTensorConstraints": "4e713e9d35a17edeb3ea0a4c6c8227fe76894294"}, "results": {}, "time": "2026-10-28T08:52:56+0800", "transitive": 0, "version": 1}
```

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
