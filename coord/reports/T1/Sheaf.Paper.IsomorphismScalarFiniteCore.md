## What changed

Proved `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.scalar_finite_core` by
combining three independently simpler construction statements. Added the finite
comparison, quotient-formula, and transition-formula modules; each records the
remaining mathematical construction as a named theorem for follow-up. The core
module imports those proof-only statements and combines their witnesses without
changing its target signature.

## Proved and sorry left

Closed 1 of 1 original sorries:
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.scalar_finite_core`.

Three strictly simpler sorries were split off:

- `finite_formula_exists`, node
  `lem-weil-isomorphism-scalar-finite-comparison-formula`;
- `quotient_formulas_exists`, node
  `lem-weil-isomorphism-scalar-finite-quotient-formulas`;
- `transition_formulas_exists`, node
  `lem-weil-isomorphism-scalar-finite-transition-formulas`.

No sorry occurs in a definition, and no axiom or unsafe declaration was added.

## No longer needed

No existing import line was removed. The core theorem no longer directly follows
the generic `scalar_quotient_chain_squares` route: its chosen finite change-of-rings
models are not definitionally the generic extension functors, so that dependency
was removed from the core node's proof route. The three split-off nodes retain the
generic quotient-chain theorem as the planned source for their separate
constructions.

## Where the brief, the DAG or earlier work was wrong

The earlier one-step plan treated the generic scalar-extension presentation as if
it were definitionally identical to the specialized `finiteChangeData`,
`integralScalarReduction`, and inverse-image models. Those presentations require a
substantial transport argument. The delivery records that argument as three
strictly simpler component statements and proves the target by their genuine
conjunction of witnesses; the target statement and unit route are unchanged.

## New nodes

`lem-weil-isomorphism-scalar-finite-comparison-formula` records existence of the
finite comparison satisfying `FiniteFormula`.

`lem-weil-isomorphism-scalar-finite-quotient-formulas` records existence of both
completed-to-finite quotient maps satisfying their local formulas.

`lem-weil-isomorphism-scalar-finite-transition-formulas` records existence of both
adjacent transition maps satisfying their local formulas.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteComparisonFormula": "6cf2ab243312d41b635d3808c4320e052a32f390", "Sheaf.Paper.IsomorphismScalarFiniteCore": "795cc3dcdd6a963af756502b0d44fe227ceb25ca", "Sheaf.Paper.IsomorphismScalarFiniteQuotientFormulas": "7c16d34c7f5f068479feaaa1ace9aa5322396c4a", "Sheaf.Paper.IsomorphismScalarFiniteTransitionFormulas": "1d34ed2a24f63a63bb8fb1809a306fc7de5c7c79"}, "results": {}, "time": "2026-10-28T07:11:50+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
