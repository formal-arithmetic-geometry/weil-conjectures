## What changed

Proved `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.right_quotient_formula_exists`
without changing its signature. Added two private proof imports, with `import all` to reuse
proved implementation lemmas: `Sheaf.Paper.FiniteFreeCompletedScalarComparison` and
`Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`.

The private `rightModuleQuotient` composes the inverse image of the canonical completed
scalar quotient with `inverseReductionTransport`. The latter is identity on sections
and is linear by the completed/finite coefficient projection square. The private
`rightComplexQuotient` lifts this transformation degreewise; naturality supplies both
the differential compatibility and naturality on complexes. Restriction to good
complexes and `completedScalarModuleArrow_tensor` finish the stated formula.
No finite-free comparison theorem or completed model existence theorem is invoked.
The construction works for arbitrary complexes and does not need the given `b` or `hb`.

Updated the item's proof plan and dependencies to the actual route. All public imports,
definitions and declaration signatures are preserved. No other existing module changes.
Validation: the complete proof compiled in 9.6 seconds before removing its sole unused
hypothesis warning; the final warning-free version is checked by the delivery tool.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.right_quotient_formula_exists`
(node `lem-weil-isomorphism-scalar-finite-right-quotient-formula`).
There are zero `sorry` declarations left in the item and zero holes added elsewhere.
The two new private definitions contain no holes. No decomposition or split-off statement.

## No longer needed

The item's proof no longer needs node
`lem-weil-isomorphism-scalar-quotient-chain-squares` or module
`Sheaf.Paper.IsomorphismScalarQuotientChainSquares`: the right component already exists
as the canonical quotient in the completed scalar construction. The general finite
comparison, left component and transition squares are unnecessary for this obligation.
That module was not previously imported here, so no import was removed. Other consumers
may still need it; no declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned generic quotient-chain specialization concealed an unnecessary presentation
transport: `completedScalarModuleArrow_tensor` already handles exactly the chosen
completed and finite tensor presentations. Combining it with the existing
`inverseReductionTransport` closes the obligation directly. The original statement is
unchanged; its completed-comparison normalization hypothesis is stronger than this
right-only construction requires. No mathematical statement is disputed and no unit
statement or realized proof step is bypassed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteRightQuotientFormula": "2920a847eca851675913ce6a2cd80ff9f54d381b"}, "results": {"Sheaf.Paper.IsomorphismScalarFiniteQuotientFormulas": {"hash": "5d472b18ecab7595a9627d061838d21729270910", "status": "OK"}}, "seconds": 89, "time": "2026-10-28T10:18:30+0800", "transitive": 0, "version": 1}
```

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
