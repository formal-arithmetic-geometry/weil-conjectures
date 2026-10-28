## What changed

Added the normalized K-flat representative square and the transport theorem as two
strictly simpler intermediate statements, then proved the assigned theorem by applying
transport to the representative square. Added proof-only imports for these modules.

## Proved and sorry left

The assigned declaration `coefficientNormalizedTensorHorizontal` is reduced to the two
named intermediate declarations. The representative declaration
`coefficientNormalizedTensorHorizontalRepresentative` remains `sorry`, and the
transport declaration `coefficientNormalizedTensorHorizontalTransport` remains `sorry`.
These are the two split-off steps.

## No longer needed

No declared proof dependency was removed; both dependencies remain represented by the
intermediate proof plan.

## Where the brief, the DAG or earlier work was wrong

The original node combines the representative pure-tensor calculation with transport
from K-flat resolutions. Those are separate obligations for the coefficient-specific
quotient calculus because its adjunction and tensor comparison are chosen data.

## New nodes

`lem-coef-normalized-tensor-horizontal-representative` records the K-flat representative
calculation. `lem-coef-normalized-tensor-horizontal-transport` records the independent
resolution transport step.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientNormalizedTensorHorizontal": "b685399b9bbd74c69eab5148a0eb3361ad4d98dd", "Sheaf.Paper.CoefficientNormalizedTensorHorizontalRepresentative": "91601277333276287f9b3f923a343bd9b398813f", "Sheaf.Paper.CoefficientNormalizedTensorHorizontalTransport": "4a47f002b8fbc5b0586dad299276e673cc5eab45"}, "results": {}, "time": "2026-10-28T08:03:47+0800", "transitive": 0, "version": 1}
```

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
