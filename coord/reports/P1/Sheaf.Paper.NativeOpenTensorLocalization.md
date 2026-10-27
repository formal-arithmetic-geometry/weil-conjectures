## What changed

Filled `native_open_tensor_localization` with a real composition proof. The argument uses two new stage-3 component modules: one states the existence of the localized derived comparisons, and one states the native presentation construction for fixed comparisons. The item module imports both components and combines their outputs.

## Proved and sorry left

The item theorem `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_localization` is proved. The two strictly smaller component theorems remain `sorry`: `native_open_tensor_comparisons` (node `new-sf-native-open-tensor-comparisons`) and `native_open_tensor_presentation_exists` (node `new-sf-native-open-tensor-presentation`).

## No longer needed

No proof-dependency imports were removed. The original generic proof dependencies are represented by the two split component nodes; no additional modules are needed by the item proof.

## Where the brief, the DAG or earlier work was wrong

The original node bundled chain localization, K-flat preservation, and all dependent presentation fields into one theorem. This was too large to elaborate directly, so the proof plan is decomposed into the two strict component statements above while preserving the original conclusion and native equalities.

## New nodes

`new-sf-native-open-tensor-comparisons` records the localized derived comparison isomorphisms. `new-sf-native-open-tensor-presentation` records construction of the native presentation from fixed comparisons.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeOpenTensorComparisons": "2c781eac2f4961eb48bf7352f521d15cfc6d0e5a", "Sheaf.Paper.NativeOpenTensorLocalization": "42fa7b23611c659ab1df840465417cb6310c4bbc", "Sheaf.Paper.NativeOpenTensorPresentationExistence": "273b1cd1530f08e4e22fbd776b7d7bf6e19e7ede"}, "results": {}, "time": "2026-10-28T00:54:25+0800", "transitive": 0, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
