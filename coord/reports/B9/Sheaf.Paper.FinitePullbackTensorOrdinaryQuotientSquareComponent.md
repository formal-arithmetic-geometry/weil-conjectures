## What changed

Filled `finitePullbackTensor_ordinary_quotient_square_component` by cancelling the ordinary
finite quotient adjunction and the inverse-image adjunction, reducing the component equality
to the fixed-degree pure generator calculation. Added the proof-only module
`Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquarePure`, which records that generator
calculation as a split theorem.

## Proved and sorry left

The item theorem `finitePullbackTensor_ordinary_quotient_square_component` is proved. One
split-off theorem remains sorry: `finitePullbackTensor_ordinary_quotient_square_pure` in
`Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquarePure`.

## No longer needed

No proof-dependency imports were removed. The component proof uses the finite pullback
K-flat normalization module and the new pure-generator split module.

## Where the brief, the DAG or earlier work was wrong

The component proof plan omitted the explicit ordinary-adjunction and inverse-image
adjunction cancellation that exposes the pure-generator calculation. The missing
calculation is now isolated as a strictly lower split theorem.

## New nodes

`lem-pur-finite-pullback-tensor-ordinary-quotient-square-pure`: fixed-degree pure-generator
calculation after the two adjunction transposes; its source is Stacks Tags 03EL, 06YY and
07A4, and its Lean declaration is in
`Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquarePure`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquareComponent": "0c191148e6f8754a4187488a25e4a4b72245588d", "Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquarePure": "d8e0077fd12ad060707e8744aa7e77d2603dbc9e"}, "results": {}, "time": "2026-10-28T08:30:37+0800", "transitive": 0, "version": 1}
```

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
