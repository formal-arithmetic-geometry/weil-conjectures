## What changed

Added two intermediate theorem modules. `IntegralPullbackReductionAugmentationGood` isolates the
normalized equation on good flat-term K-flat representatives. `IntegralPullbackReductionAugmentationDescent`
is the localization descent statement. The target module now obtains the comparison from the first
statement and applies the second; the existing uniqueness proof is unchanged.

## Proved and sorry left

The target theorem `pullbackReductionAugmentation_exists` is closed by decomposition into the two
named intermediate statements below. The existing `pullbackReductionAugmentation_existsUnique` and
`pullbackReductionComparison` remain proved. Two strictly simpler proof obligations remain as
`sorry`: `pullbackReductionAugmentation_good` and `pullbackReductionAugmentation_of_good`.

## No longer needed

No imports or existing DAG proof dependencies were removed. The original monolithic representative
and localization steps are replaced by the two intermediate nodes, which are the only new proof
imports used by the target theorem.

## Where the brief, the DAG or earlier work was wrong

The original node presented representative construction and localization descent as one theorem,
although the module's own proof description separates these into independent steps. The delivery
records that decomposition explicitly; no target statement or definition was changed.

## New nodes

`lem-sf-pullback-reduction-augmentation-good` records the good-representative normalized adjunct
calculation. `lem-sf-pullback-reduction-augmentation-descent` records descent of that equation through
the good-complex localization. Both nodes have matching Lean declarations and proof-source
annotations in the sandbox DAG.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralPullbackReductionAugmentation": "beab41e42c31ad37776a8dd78423905ca1de8615", "Sheaf.Paper.IntegralPullbackReductionAugmentationDescent": "fdaff29408cae3b89555b6e3617c9724df00cc67", "Sheaf.Paper.IntegralPullbackReductionAugmentationGood": "f80701fafa98351ef3504442773722289477988b"}, "results": {}, "time": "2026-10-28T04:10:37+0800", "transitive": 0, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
