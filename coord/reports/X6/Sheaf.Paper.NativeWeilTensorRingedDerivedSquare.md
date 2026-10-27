## What changed

Filled the assigned theorem by combining two strict intermediate results. The ordinary
intermediate theorem supplies the one-K-flat ordinary representative model, its
`NativeAdjunctionNormalization`, and representative naturality. The native intermediate
theorem supplies the tensor-forgetting isomorphism, the displayed
`NativeWeilRingedModelForget` square, and `TensorCoherence`. The parent theorem packages
these results into its original conjunction without changing its statement.

Added the proof-only imports and the two new `Sheaf` modules that carry the intermediate
statements. Updated the assigned DAG node's proof and dependencies to record this route.

## Proved and sorry left

The assigned declaration
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square` is proved
from the two strict intermediate statements.

Two split-off theorem proofs remain as documented obligations:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_ordinary_data`
  in node `lem-sf-native-weil-tensor-ringed-derived-square-ordinary-data`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_native_data`
  in node `lem-sf-native-weil-tensor-ringed-derived-square-native-data`.

No definition contains `sorry`.

## No longer needed

No imports were removed. The assigned proof uses the existing ringed bridge, native
ringed model, native model naturality, native forgetting K-flatness, ringed tensor
transposition descent, and the K-flat replacement dependencies named in the two new
DAG proof plans. No declared dependency was bypassed below the unit level.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines two long constructions in one theorem and did not expose
the ordinary representative construction as a separately usable statement. The delivery
keeps the plan's route and separates it into the ordinary and native components; the
parent proof is then a direct categorical packaging step. The assigned target statement
and all existing definitions are unchanged.

## New nodes

`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-data` records the ordinary
one-K-flat model, normalization, and naturality obligation in
`lean/Sheaf/Paper/NativeWeilTensorRingedDerivedSquareOrdinary.lean`.

`lem-sf-native-weil-tensor-ringed-derived-square-native-data` records the native
representative square and coherence obligation in
`lean/Sheaf/Paper/NativeWeilTensorRingedDerivedSquareNative.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquare": "5b025cfd7e4859282042e936f945814922d493b6", "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative": "ce1310d4acdfb40d8efde960b5923a83845c1bcd", "Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary": "bb38cdbad063cdd3ef9ca8461bb0929ba2924b2f"}, "results": {}, "time": "2026-10-28T00:10:15+0800", "transitive": 0, "version": 1}
```

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
