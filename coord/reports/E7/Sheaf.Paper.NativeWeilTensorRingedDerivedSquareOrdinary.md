## What changed

Repaired the returned route. The old normalization-only lemma was replaced by
K-flat-input naturality in `Sheaf.Paper.NativeOrdinaryTensorModelNaturality`.
Added `Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension`, which imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` and states the
K-flat-resolution extension. The assigned theorem now extracts the supplied
normalized model, proves its K-flat-input naturality, and obtains a new extended
`ordinaryModel` with normalization and naturality for arbitrary second inputs.
The assigned node's Lean statement now records the live `hS` binder.

## Proved and sorry left

The assigned declaration
`native_weil_tensor_ringed_derived_square_ordinary_data` is proved by applying the
two split-off steps. Two strictly smaller proof obligations remain sorry:

- `native_ordinary_tensor_model_naturality_kflat`, naturality when both second
  inputs are K-flat;
- `native_ordinary_tensor_model_resolution_extension`, extension through
  degreewise-epimorphic K-flat resolutions to arbitrary second inputs.

## No longer needed

`lem-sf-kinjective-hom-comparison-descent` remains pruned. The previously pruned
`lem-pc-kflat-resolution` is restored as a proof dependency of both the
K-flat-input route and the resolution-extension route.

## Where the brief, the DAG or earlier work was wrong

The returned review correctly identified that normalization only constrains the
model on K-flat second inputs; it cannot imply naturality for arbitrary inputs.
The repair restores the K-flat replacement argument and chooses a new extended
ordinary model.

## New nodes

`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`
records the K-flat-resolution extension. The existing naturality node was repaired
to record the strictly smaller K-flat-input statement.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryTensorModelNaturality": "fb5064fc53d5fa0f9541cf3250f9ab5b9f8f51d6", "Sheaf.Paper.NativeOrdinaryTensorModelResolutionExtension": "9bc35385c10cae455608bf6570836efcf37890ea", "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary": "af87fe66681c87b5d0b0569238322b35c44dd359"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquare": {"hash": "5b025cfd7e4859282042e936f945814922d493b6", "status": "OK"}, "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative": {"hash": "ce1310d4acdfb40d8efde960b5923a83845c1bcd", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T04:27:41+0800", "transitive": 0, "version": 1}
```

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
