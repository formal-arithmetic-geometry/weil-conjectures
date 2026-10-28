## What changed

Proved `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.left_quotient_formula_exists`
in the assigned module. The left map is the composite of the supplied completed
comparison, the existing right quotient map, and the inverse of the restricted
finite comparison. Its formula follows from the two normalization formulas,
compatibility of coefficient projections with inverse image, and inverse cancellation.

Added proof-only imports of `Sheaf.Paper.IsomorphismScalarFiniteComparisonUnit`,
`Sheaf.Paper.IsomorphismScalarFiniteRightQuotientFormula`, and
`Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison` (the last with
`import all` to use its proved private coefficient square). Statements, definitions,
visibility, and public imports are unchanged. Updated the item's DAG proof and
proof dependencies to match this argument.

Validation: the final module compiled on the project server in 12.7 seconds.
The construction works uniformly at n = 0, for zero complexes, and on empty sites;
it uses no surjectivity or flatness of coefficient projections.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.left_quotient_formula_exists`
(node `lem-weil-isomorphism-scalar-finite-left-quotient-formula`).
There are zero `sorry` occurrences left in the delivered module and zero new
holes or split-off statements. The proof uses the already stated
`finite_formula_unit_exists` and `right_quotient_formula_exists`; their existing
unproved bodies remain the separate tasks assigned to those modules.

## No longer needed

The item no longer directly needs the planned
`lem-weil-isomorphism-scalar-quotient-chain-squares` /
`Sheaf.Paper.IsomorphismScalarQuotientChainSquares`: its presentation transport
is replaced by the existing project-specific unit finite comparison and right
quotient declarations. No original public or proof import was removed.

The full finite formula and its arbitrary-middle-coefficient extension
(`lem-weil-isomorphism-scalar-finite-comparison-formula` and
`lem-weil-isomorphism-scalar-finite-comparison-formula-extension`) are unnecessary
for this proof; only the unit case is used. These nodes and the generic quotient
chain node still have other consumers, so this delivery withdraws no module and
makes no claim of global pruning.

## Where the brief, the DAG or earlier work was wrong

The old plan treated the left formula as an independent presentation-transport
construction. Once the right quotient and unit finite comparison are stated,
conjugation gives the left map and its normalization directly. This is the same
left-map construction described in Step 4 of the generic quotient-chain node,
but applied to the already selected concrete presentations. No further split is
needed. The assigned node does not realize a unit statement or unit proof step;
the unit route is preserved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteLeftQuotientFormula": "870208d37245518d21c89a182c8c890d3ce17cf3"}, "results": {}, "time": "2026-10-28T10:36:59+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
