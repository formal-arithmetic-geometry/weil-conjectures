## What changed

Replaced the remaining proof of `wfTensorCompletionFrobenius_exists` by a real assembly from two named intermediate obligations: existence of a normalized rational comparison package and the Weil compatibility property of any normalized package. Both obligations are documented and recorded as new DAG nodes.

## Proved and sorry left

The original `wfTensorCompletionFrobenius_exists` hole is closed by combining the two intermediate theorems and the existing uniqueness theorem. Two strictly smaller obligations remain as `sorry`: `wfTensorCompletionFrobenius_normalized_exists` and `wfTensorCompletionFrobenius_weil_property`.

## No longer needed

None. The existing tensor, constructibility, pullback-unit-square, and uniqueness dependencies remain needed by the decomposed proof route.

## Where the brief, the DAG or earlier work was wrong

The prior source-level proof description bundled scalar-localized bifunctor construction, normalization, and Weil-pair lifting into one theorem-sized obligation. The delivery exposes the two independent obligations so they can be proved separately; the target statement and all existing definitions are unchanged.

## New nodes

- `lem-wf-tensor-completion-frobenius-rational-normalized-existence`
- `lem-wf-tensor-completion-frobenius-weil-property`

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 3 OK, 1 SLOW.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.WfTensorCompletionFrobenius": "263616afcce7c719e17756f5a56f02f683140f2b"}, "results": {"Sheaf.Paper.CompactSupportProjectionFormula": {"hash": "9d8a08bf4a6d4025a7ffc9ce8b51e70bcc8ad44a", "status": "OK"}, "Sheaf.Paper.ProjectionRationalTensorDescent": {"hash": "bc5e701300fee22ec664dd58eeb82f7145f0a2c3", "status": "OK"}, "Sheaf.Paper.ProjectionTensorCoefficientComparison": {"hash": "1b3f917c718a23cd0c8025ed4ef15d7d7f6e6f1c", "status": "OK"}, "Sheaf.Paper.ProjectionWeilTensorDomainBridge": {"hash": "ff2e4ac76a3581b5777f72de17fb80ec5a21c6b9", "status": "SLOW"}}, "seconds": 161, "time": "2026-10-28T03:41:09+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
