## What changed

Filled `WeilConjectures.IntegralHom.reduction_target_exists`.  The proof obtains the
finite-coefficient closed symmetric monoidal data from
`ringedDerived_closed_symmetric_monoidal`, transports its tensor-Hom adjunction
across the braiding, and assembles the `TensorPresentation`.  The representative
evaluation field is isolated in the new module
`Sheaf.Paper.FiniteTensorPresentationEvaluation`.

## Proved and sorry left

Closed the one original sorry, `reduction_target_exists`.  Added one strictly
smaller split-off theorem, `finite_tensor_presentation_evaluation`, whose proof
is left as one sorry for the representative-level signed evaluation construction.

## No longer needed

Removed the proof-only imports
`Sheaf.Paper.IntegralHomTensorPresentationAdjunction` and
`Sheaf.Paper.IntegralHomTensorPresentationEvaluation`.  Those modules provide the
completed-coefficient route and are not used by the finite-coefficient target
construction here.

## Where the brief, the DAG or earlier work was wrong

The parent plan described scalar extension and restriction as if the finite
representative evaluation were already available.  The generic ringed-derived
closed symmetric monoidal construction directly supplies the finite tensor data
and the adjunction; only the representative evaluation normalization requires a
separate intermediate statement.  No target statement was changed.

## New nodes

Added `new-sf-integral-hom-reduction-target-evaluation` for
`Sheaf.Paper.FiniteTensorPresentationEvaluation`, with the finite-level signed
evaluation formula and comparison-counit equation as its statement.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteTensorPresentationEvaluation": "15b0cfa4dc74d8bfa97530ba94a850d5565491ee", "Sheaf.Paper.IntegralHomReductionComponents": "70f846f8d425d49a391ffa42d0a3c297b4e68279"}, "results": {"Sheaf.Paper.IntegralHomReductionPresentation": {"hash": "0e5216560a3b2842e8613af3378b2363613c69c3", "status": "OK"}}, "seconds": 7, "time": "2026-10-28T11:15:54+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
