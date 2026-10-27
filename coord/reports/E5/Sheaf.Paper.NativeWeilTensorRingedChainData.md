## What changed

- Corrected `native_weil_tensor_ringed_chain_data` to require the normalized Koszul scalar action for `sign`; the old arbitrary-sign statement is false.
- Added `Sheaf.Paper.NativeWeilTensorRingedUnderivedIso`, whose split theorem supplies a natural bifunctor isomorphism with components `U.underived`.
- Added `Sheaf.Paper.NativeWeilTensorRingedChainLaws`, whose split theorem records the signed summand and naturality laws for the generic total comparison.
- The item now constructs the total isomorphism using `HomologicalComplex.mapBifunctorComparison` and `mapBifunctorFlipIso`, then assembles the split laws.
- Adapted `Sheaf.Paper.NativeWeilTensorRingedComplexes` to pass the normalization proof for `nativeRingedTensorSign`.

## Proved and sorry left

The item theorem `native_weil_tensor_ringed_chain_data` is proved with no `sorry`. The delivery adds two named split-off theorems, each intentionally left as `sorry`: `native_weil_tensor_ringed_underived_iso` in node `lem-sf-native-weil-tensor-ringed-underived-iso`, and `native_weil_tensor_ringed_chain_laws` in node `lem-sf-native-weil-tensor-ringed-chain-laws`.

## No longer needed

The proof uses the stated underived-data node and the generic Mathlib homological-complex comparison and flip APIs. No prior native chain-comparison module or extra imports are needed; the direct `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor` import remains because the proof uses those declarations.

## Where the brief, the DAG or earlier work was wrong

The original node allowed an unconstrained `sign` function. This is too strong: a function assigning zero to a nonzero morphism contradicts the required isomorphism summand formula. The statement was corrected with a `statement_change` record; the parent node's route is preserved.

## Forced adaptations

`Sheaf.Paper.NativeWeilTensorRingedComplexes` previously called the theorem with only `nativeRingedTensorSign b`. Its unchanged theorem signature still compiles after the forced extra argument `(by intro p q Y Z f; rfl)`, which establishes that this existing sign is exactly the normalized scalar action. No other module was edited.

## New nodes

- `lem-sf-native-weil-tensor-ringed-underived-iso` — `coord/changes/` is unchanged; its new module carries the underived naturality split.
- `lem-sf-native-weil-tensor-ringed-chain-laws` — `coord/changes/` is unchanged; its new module carries the signed summand and naturality split.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedChainData": "db90026f589c7d4d8ee1e1f145463eac2eaf24b1", "Sheaf.Paper.NativeWeilTensorRingedChainLaws": "4eca42a55a833dbe7299cc4876cb7e1651ced261", "Sheaf.Paper.NativeWeilTensorRingedComplexes": "79740456a66aae79a1534d4c6039485e6318f295", "Sheaf.Paper.NativeWeilTensorRingedUnderivedIso": "8a315e43f3e843831a2004ac8b242e867cc8dd90"}, "results": {}, "time": "2026-10-28T04:51:48+0800", "transitive": 0, "version": 1}
```

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
