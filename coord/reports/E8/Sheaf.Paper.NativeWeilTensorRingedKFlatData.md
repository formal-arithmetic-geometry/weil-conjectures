## What changed

The target theorem now assembles a `NativeWeilRingedTensorKFlatData` record from two
strict proof interfaces.  The target module imports the two new proof-only modules and
constructs the record field by field.  The new modules isolate K-flat transport and
native localization respectively; both retain the exact field types of the original
record.  The target node's proof and proof dependencies were updated to this route.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_data`,
the sole sorry in the item.  Two strictly simpler lower statements remain as named
sorries:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_flat`, node
  `lem-sf-native-weil-tensor-ringed-kflat-flat`;
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_localization`,
  node `lem-sf-native-weil-tensor-ringed-kflat-localization`.

The final proof is complete Lean code and depends only on these two lower statements.

## No longer needed

No imports were removed.  The direct item proof no longer cites
`lem-pc-kflat-resolution`; that dependency remains required by both split interfaces,
so it is still in the transitive proof route.  No existing module or declaration was
pruned.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan bundled two independent record fields: transport of
acyclic-test K-flatness and localization by native K-flat replacements.  Neither field
is stated by the bridge or the generic resolution declaration alone.  Splitting these
fields gives two strictly smaller obligations while preserving the item statement and
its unit route.

## New nodes

`lem-sf-native-weil-tensor-ringed-kflat-flat` records the K-flat transport field and is
stated in `lean/Sheaf/Paper/NativeWeilTensorRingedKFlatFlat.lean`.

`lem-sf-native-weil-tensor-ringed-kflat-localization` records the localization field
and is stated in `lean/Sheaf/Paper/NativeWeilTensorRingedKFlatLocalization.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedKFlatData": "1fa1cdc7b7fa69f856d5048456ed076934393353", "Sheaf.Paper.NativeWeilTensorRingedKFlatFlat": "e15ad3aabd0a4ffba753d8ddebfefc7f807ea1fa", "Sheaf.Paper.NativeWeilTensorRingedKFlatLocalization": "d6b474dee1b1c4f9fdf17ed944374cdc3b7346b6"}, "results": {}, "time": "2026-10-28T04:15:50+0800", "transitive": 0, "version": 1}
```

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
