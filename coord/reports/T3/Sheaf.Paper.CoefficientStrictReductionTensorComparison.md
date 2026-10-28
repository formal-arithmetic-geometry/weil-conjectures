## What changed

Proved `WeilConjectures.coefficientStrictReductionTensorComparison_exists` in
`Sheaf.Paper.CoefficientStrictReductionTensorComparison` by the existing record
field `R.reductionTensor`. Its type is exactly the requested isomorphism. Updated
its DAG proof and proof dependencies to this direct projection argument.

Marked `coefficientStrictReductionTensorNormalization_of` as STATEMENT-DISPUTED
without changing its signature or proof body. No imports or interfaces changed.
The assigned queue row is stage 3 / proof / route; there is no matching rework row
or build-error file in the shared snapshot.

Validation: the item compiled through `lcompile.py` in 3.6 seconds, exit code 0.
Searches through msearch leanfinder and loogle, plus rg over the project, confirmed
that only Nonempty.intro and the existing reductionTensor field are needed.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.coefficientStrictReductionTensorComparison_exists`
(node `lem-coef-strict-reduction-tensor-comparison`).

One original hole remains:
`WeilConjectures.coefficientStrictReductionTensorNormalization_of`
(node `lem-coef-strict-reduction-tensor-normalization-fixed`). This is disputed
for the reason below. No holes added and no obligations split off.

## No longer needed

The existence node no longer needs
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, whose module is
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the input already
carries the required isomorphism. Removed that planned proof dependency from the
existence node. This is local pruning of its proof route, not a claim that the
general tensor-pullback module is globally unreachable or unnecessary for the
remaining normalization construction. No Lean imports removed, no declarations
withdrawn, and no unit statement or realized unit step bypassed.

## Where the brief, the DAG or earlier work was wrong

The existence node planned a derived tensor construction even though
CoefficientDerivedSystemReduction already has a reductionTensor field of the
exact asserted type. Its existence proof therefore has no remaining construction
obligation.

STATEMENT-DISPUTED: coefficientStrictReductionTensorNormalization_of quantifies
over EVERY isomorphism μ, with no hypothesis that it is induced by the strict
chain construction. The associated node's prose and theorem docstring restrict
to comparisons supplied by that construction, but its Lean signature has no
such condition. The reduction record also imposes no normalization condition on
its reductionTensor field.

The obstruction is a scalar twist: for the usual coefficient models, negating a
comparison gives another natural isomorphism. It reverses its finite pure-tensor
map, whereas the definition of CoefficientReductionTensorNormalization fixes
that map to coefficientScalarTensorIso. On degree-zero coefficient units with
odd residue characteristic (for example l = 3), the prescribed maps 1 and -1
are different. Varying the presentations cannot remove this: the three
CoefficientReductionPresentation clauses pin them to the SAME reductionEvaluation,
and the finite chain equation pins ψ. The existing proof in
CoefficientReductionTensorEvaluationPasting shows explicitly that these
normalizations determine the evaluated comparison once the finite and evaluation
comparisons are normalized. Thus both a comparison and its negative cannot meet
the required normalization on a nonzero coefficient unit. This edge-case argument
is mathematical; no Lean formalization of the concrete nonzero-unit example is
claimed in this delivery.

CoefficientNormalizedReductionNormalizations already documents and repairs the
same arbitrary-comparison defect for finiteTensor by constructing normalized
comparisons instead of normalizing every possible one. The surviving upper
coefficientStrictReductionTensorNormalization theorem likewise asks only for
existence of a normalized comparison, which is the appropriate construction
obligation. This delivery does not replace it with another equivalent hole or
use the disputed theorem to derive a false normalization. The disputed existing
hole is preserved for an explicit statement repair and construction.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientStrictReductionTensorComparison": "cf58b81e1d3621e5b8b8ec33111229f6eb9bbcd7"}, "results": {}, "time": "2026-10-28T11:58:58+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
