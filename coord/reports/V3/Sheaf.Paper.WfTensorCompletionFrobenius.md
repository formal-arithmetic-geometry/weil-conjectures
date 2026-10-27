## What changed

Retained the existing normalized comparison decomposition and simplified the assembly
proof of `wfTensorCompletionFrobenius`: the existence witness is used directly as the
normalization conjunct, and uniqueness is applied to the two full properties. The
statement and all public definitions are unchanged. The common-field theorem remains
an open obligation.

## Proved and sorry left

`WeilConjectures.wfTensorCompletionFrobenius` is proved by combining the two named
intermediate declarations. The following three declarations remain `sorry`:

- `WeilConjectures.wfTensorCompletionFrobenius_exists`;
- `WeilConjectures.wfTensorCompletionFrobenius_unique`;
- `WeilConjectures.wfTensorCompletionCommonField`.

No new `sorry` was added.

## No longer needed

None. All imports and declared dependencies remain required by the module.

## Where the brief, the DAG or earlier work was wrong

The live source already contains the decomposition of the target into existence and
uniqueness obligations. The remaining obligations require the full rational tensor
construction and common-field descent and cannot be discharged by the assembly step.

## New nodes

None.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
