# Completion finite extension tensor bijective scope

## Reason

The proof uses tensor-product notation and therefore adds `open scoped TensorProduct`.
The command is visible to importers, so the stage-3 preflight requires this record even
though the theorem statement and all public declarations are unchanged.

## Old

The module had no `open scoped TensorProduct` command.

## New

The module opens the existing Mathlib `TensorProduct` notation scope for its proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.CompletionFiniteExtensionTensorBijective | S1 | Proof notation scope only; theorem signatures are unchanged. |
| Sheaf.RingTheory.CompletionFiniteExtensionTensor | unclaimed | Direct importer and user of completion_finite_extension_tensor_bijective; its signatures are unchanged and it compiles against the delivery without adaptation. |

## Status

landed 20261012T223416-L-1640660 2026-10-12 (merge of deliver/S1/Sheaf.RingTheory.CompletionFiniteExtensionTensorBijective)
