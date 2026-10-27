## What changed

Proved `WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_ordinary_supported` from the
invertibility of the native extension counit on the ordinary tensor. Added the proof-only
module `Sheaf.Paper.CoefNativeOpenTensorOrdinaryCounit`, whose intermediate theorem records
that categorical counit step and remains the sole `sorry` in the delivery. The target module
keeps its two public imports because its statement uses the coefficient-site definitions;
the new counit module is imported privately for the proof.

## Proved and sorry left

Closed the target declaration
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_ordinary_supported` (1 hole).
Added one strictly intermediate theorem, still `sorry`:
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_ordinary_counit_isIso` in
`lem-coef-native-open-tensor-ordinary-counit` (1 split-off hole).

## No longer needed

The target proof no longer directly uses the three original proof dependencies
`lem-weil-proetale-weakly-etale-localization`, `def-sp-varying-ring-operations`, and
`lem-weil-pbc-ringed-slice-extension-tensor`; their content is isolated in the new
counit theorem. No public statement imports were removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan left the transport and counit calculation implicit. The
implemented proof makes the categorical intermediate explicit, then uses the standard
`Functor.essImage.ofIso` construction. No statement was weakened or changed.

## New nodes

`lem-coef-native-open-tensor-ordinary-counit` records the native projection-formula
counit isomorphism from Stacks Tag 0E8I. Its Lean declaration is in
`lean/Sheaf/Paper/CoefNativeOpenTensorOrdinaryCounit.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefNativeOpenTensorOrdinaryCounit": "f79ec80beb633fa9cbff8c77807ce451a7588724", "Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported": "8d381b6139b92b1537f8723cb6d21e1e91107d39"}, "results": {"Sheaf.Paper.CoefNativeOpenTensorSystemExistence": {"hash": "865ed89b62dc7c45ef0de9af083813b4df5754ca", "status": "OK"}}, "seconds": 57, "time": "2026-10-28T05:33:32+0800", "transitive": 0, "version": 1}
```

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
