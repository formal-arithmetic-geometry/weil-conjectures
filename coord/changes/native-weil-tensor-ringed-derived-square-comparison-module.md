# native_weil_tensor_ringed_derived_square_comparison module placement

## Reason
The comparison proof was moved out of the assigned module so that the assigned
coherence assembly and the comparison each compile within the stage-3 file limit.
The declaration and its statement are unchanged; only its module attachment and
private helper scope change.

## Old
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_comparison`
was declared in `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative`.

## New
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_comparison`
is declared in `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNativeComparison`.
The assigned module imports that proof-only module and uses the unchanged theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative` | B4 | imports the new proof-only module and applies the unchanged comparison theorem |
| `Sheaf.Paper.NativeWeilTensorRingedDerivedSquare` | unclaimed | no source change; it continues to import the assigned module and use the native data theorem |

## Status
landed 20261027T233802-L-4114713 2026-10-27 (merge of deliver/B4/Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative)
