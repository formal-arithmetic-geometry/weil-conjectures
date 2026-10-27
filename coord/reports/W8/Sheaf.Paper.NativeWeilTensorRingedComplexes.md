## What changed

Restored the quarantined `Sheaf.Paper.NativeWeilTensorRingedComplexes` source and replaced its
open theorem proof with a complete assembly proof. The proof imports three proof-only
interfaces: underived evaluation normalization, signed total-complex comparison, and
K-flat localization. Each interface is a strict part of the original structure and is
assembled field-by-field into `NativeWeilRingedTensorComplexes`.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_complexes` (one
sorry). Three strict intermediate statements remain open:

- `native_weil_tensor_ringed_underived_data`, node
  `lem-sf-native-weil-tensor-ringed-underived-data`;
- `native_weil_tensor_ringed_chain_data`, node
  `lem-sf-native-weil-tensor-ringed-chain-data`;
- `native_weil_tensor_ringed_kflat_data`, node
  `lem-sf-native-weil-tensor-ringed-kflat-data`.

Thus one of one sorries in the item was closed and three lower sorries were added as a
strict decomposition.

## No longer needed

The explicit proof dependency `lem-pc-kflat-resolution` is no longer used by the
assembly route: its K-flat resolution argument is isolated in the open K-flat interface.
The existing presentation API remains transitively required for `NativeTensorKFlat`, and
the bridge API remains required by all three intermediate interfaces.

## Where the brief, the DAG or earlier work was wrong

The quarantined module was an interface-only landing whose proof obligation combines three
independent constructions. Treating it as one direct theorem obscured the strict
underived, chain, and localization boundaries. The item statement and all existing
signatures were retained unchanged; the DAG copy now records the three-interface route.

## New nodes

`lem-sf-native-weil-tensor-ringed-underived-data` records the underived comparison and its
uncurrying equation, in `NativeWeilTensorRingedUnderivedData.lean`.

`lem-sf-native-weil-tensor-ringed-chain-data` records the total comparison, signed summand
formula, and naturality, in `NativeWeilTensorRingedChainData.lean`.

`lem-sf-native-weil-tensor-ringed-kflat-data` records K-flat transport and localization,
in `NativeWeilTensorRingedKFlatData.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedChainData": "0353c371fcad6e5d7b40e2ba756850253b62adaa", "Sheaf.Paper.NativeWeilTensorRingedComplexes": "4dba7c65b979505be7efd28c9adc9ea356b39787", "Sheaf.Paper.NativeWeilTensorRingedKFlatData": "e62e5986f20d491b2ce54b0c57bba2020b0fa14c", "Sheaf.Paper.NativeWeilTensorRingedUnderivedData": "1cb58bdc4dd5fd4857c103c09c700ab8412a6071"}, "results": {}, "time": "2026-10-28T01:23:29+0800", "transitive": 0, "version": 1}
```

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
