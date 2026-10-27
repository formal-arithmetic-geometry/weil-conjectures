## What changed

Added the fixed-degree component module
`Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquareComponent`.  The original
chain-map theorem now reduces its equality to `HomologicalComplex.Hom.ext` and
invokes the component theorem in each degree.  The component calculation is
split off with its generator-normalization hypotheses unchanged.

## Proved and sorry left

Closed: 1 of 1 holes in
`WeilConjectures.finitePullbackTensor_ordinary_quotient_square`.
Added: 1 strictly simpler hole in
`WeilConjectures.finitePullbackTensor_ordinary_quotient_square_component`, node
`lem-pur-finite-pullback-tensor-ordinary-quotient-square-component`.
The component theorem is the only `sorry` left in the delivery.

## No longer needed

The original theorem's direct proof dependencies are no longer needed by its
proof body; its node now depends on the component node.  They remain imported by
the component statement and are therefore retained there.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan treated the full chain-map equality as one calculation.  The
Lean proof can be assembled cleanly by first proving the fixed-degree component
calculation and then applying homological-complex extensionality.  No target
statement or existing declaration was changed.

## New nodes

`lem-pur-finite-pullback-tensor-ordinary-quotient-square-component` records the
fixed-degree component equality, with its Lean declaration in
`lean/Sheaf/Paper/FinitePullbackTensorOrdinaryQuotientSquareComponent.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquare": "66390ce851e1767b536d8c4516abc00b7e709ed5", "Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquareComponent": "3663670054e85db95f2ca2237d47362de277d7fd"}, "results": {}, "time": "2026-10-28T06:29:48+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
