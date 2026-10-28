## What changed

Repaired `commonProjectionOpenPullbackTensor_forward` by making its displayed
compatibility equation an explicit implication premise. The original theorem was
false for independent `mu` and `mu'`. The theorem is now proved by `intro h; exact h`.

Added the split module
`Sheaf.Paper.CommonProjectionOpenPullbackTensorCompatibility`, whose concrete
representative equation is used by the adapted
`Sheaf.Paper.CommonProjectionOpenPullbackTensor` proof before applying the generic
lemma and the existing inverse-square cancellation. The public statement of the
parent theorem is unchanged. The parent node's proof dependencies now include the
new compatibility node.

## Proved and sorry left

Proved `commonProjectionOpenPullbackTensor_forward` (one original `sorry` closed).
The adapted parent proof compiles unchanged in statement and has no new `sorry`.

One strictly smaller theorem remains as a named `sorry`:
`commonProjectionOpenPullbackTensor_forward_compatibility` in node
`lem-sf-common-projection-open-pullback-tensor-forward-compatibility`.

## No longer needed

No imports were removed. The generic forward theorem itself needs only its explicit
compatibility premise, so it has no proof-only imports. The parent now uses the new
concrete compatibility module and no longer relies on the false unconditional
forward assertion. No declared lower dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original declaration and DAG description omitted the compatibility hypothesis
needed for arbitrary `mu` and `mu'`; a one-object category with two endomorphisms is
a counterexample. The correction is recorded in the node's `statement_change` and
in `coord/changes/common-projection-open-pullback-tensor-forward.md`. The concrete
compatibility calculation is split off as a strictly smaller representative equation
for a later worker.

## New nodes

`lem-sf-common-projection-open-pullback-tensor-forward-compatibility` records the
concrete finite-stage representative equation used by the parent inverse-square
proof. Its Lean declaration is
`WeilConjectures.commonProjectionOpenPullbackTensor_forward_compatibility`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CommonProjectionOpenPullbackTensor": "19212b68bc063d91da0843f7ff3f216c656edf88", "Sheaf.Paper.CommonProjectionOpenPullbackTensorCompatibility": "8262d925dd365757927111c77ea52cf9fc10e7b2", "Sheaf.Paper.CommonProjectionOpenPullbackTensorForward": "610a7920aedd868960803d066e0c3a7d125f5fa3"}, "results": {}, "time": "2026-10-28T08:08:38+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
