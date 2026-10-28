## What changed

Proved `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.transition_formulas_exists`
without changing its statement. The right transition transports the existing
`integralScalarTransition` through the sectionwise inverse image and the canonical
restriction comparison. The left transition is its conjugate through the finite
comparison supplied by `finite_formula_exists`. Coefficient naturality and the
finite pure-tensor formula prove its rule. All additional helpers are private and
proved; the added imports are proof-only. The DAG now records this route.
The delivered module compiles without warnings in 34.8 seconds via `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes: `transition_formulas_exists` (node
`lem-weil-isomorphism-scalar-finite-transition-formulas`). Added zero holes;
none remain in the delivered module. The proof uses the existing
`finite_formula_exists` obligation, which is unchanged and is not claimed proved
by this delivery.

## No longer needed

No existing import was removed. The item no longer directly needs
`lem-weil-isomorphism-scalar-quotient-chain-squares` or its module
`Sheaf.Paper.IsomorphismScalarQuotientChainSquares`: specializing its full
comparison/quotient/transition package requires identifying additional chosen
presentations. Reusing the existing specialized finite comparison and scalar
transition avoids that specialization here. The generic node remains a planned
dependency of the finite-comparison item; no global withdrawal is claimed.
No unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the identification between the generic extension
functors and the chosen concrete finite models. The existing specialized scalar
transition gives the right map directly after transporting scalar restriction.
The original docstring described an independent construction of the left map;
the delivered proof instead conjugates by the finite comparison, as in the
quotient-chain argument. This works at n = 0 as well as higher levels, for zero
complexes and arbitrary pure tensors. No flatness or surjectivity is invoked.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteTransitionFormulas": "e48ea0ba683d7c94e47b7c3d15bd741ee20f29c6"}, "results": {"Sheaf.Paper.IsomorphismScalarFiniteCore": {"hash": "795cc3dcdd6a963af756502b0d44fe227ceb25ca", "status": "OK"}}, "seconds": 57, "time": "2026-10-28T07:59:21+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
