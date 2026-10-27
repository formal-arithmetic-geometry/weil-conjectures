## What changed

The item theorem now combines two strict sub-conclusions: derived unit normalization and ordinary forgetting normalization. These are stated in the new modules `Sheaf.Paper.NativeOpenTensorUnitNormalization` and `Sheaf.Paper.NativeOpenTensorForgetNormalization`, imported privately by the item. Their proofs remain named, sourced split statements for parallel completion; the item proof itself is complete and simply pairs them.

## Proved and sorry left

The item declaration `native_open_tensor_normalization` is proved. Two strictly simpler holes were added: `native_open_tensor_unit_normalization` in `new-lem-sf-native-open-tensor-unit-normalization`, and `native_open_tensor_forget_normalization` in `new-lem-sf-native-open-tensor-forget-normalization`.

## No longer needed

No declared dependency was removed. The parent proof now depends on the two new strict sub-conclusions rather than directly naming the lower localization and generic tool nodes.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the derived unit equation and the ordinary forgetting record as one opaque normalization theorem. They are independent conclusions with separate proof obligations, so the item is decomposed into those two strict statements. No target or existing statement was changed.

## New nodes

`new-lem-sf-native-open-tensor-unit-normalization` records the derived unit-transpose conclusion.

`new-lem-sf-native-open-tensor-forget-normalization` records the ordinary forgetting-data conclusion.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeOpenTensorForgetNormalization": "f93c98f5a3742a6d46bbc4df3e5911b4637f9297", "Sheaf.Paper.NativeOpenTensorNormalization": "f08a9fdb0425acbb38206b2e3d9a405a8d3b8729", "Sheaf.Paper.NativeOpenTensorUnitNormalization": "41d639f02905b88889cfae0e43d006626b88aab7"}, "results": {}, "time": "2026-10-27T23:40:04+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
