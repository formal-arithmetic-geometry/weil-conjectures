## What changed

The item module now proves `coefficientNormalizedReductionModels` by composing two
strictly smaller construction statements.  `CoefficientNormalizedReductionCore`
provides the reduction record, its prescribed tensor record, and the finite quotient
calculus.  `CoefficientNormalizedReductionNormalizations` supplies the four tensor
normalization predicates.  The item imports both proof-only modules; its public
statement imports are unchanged.

## Proved and sorry left

The item theorem `WeilConjectures.coefficientNormalizedReductionModels` is proved.
The two construction lemmas remain split statements with `sorry` proofs:
`WeilConjectures.coefficientNormalizedReductionCore` (node
`lem-coef-normalized-reduction-models-core`) and
`WeilConjectures.coefficientNormalizedReductionNormalizations` (node
`lem-coef-normalized-reduction-models-normalizations`).  No sorry occurs in a
definition.

## No longer needed

No imports or declared proof dependencies were removed.  The original broad proof
plan is represented by the two split proof dependencies recorded in the item node.

## Where the brief, the DAG or earlier work was wrong

The original item bundled the sequence-projection construction, finite quotient
calculus, and four representative tensor normalizations into one theorem.  Those
are independent proof steps, so the delivery records them as two named strictly
smaller statements while preserving the target statement unchanged.

## New nodes

`lem-coef-normalized-reduction-models-core` records the core reduction and finite
quotient construction.  `lem-coef-normalized-reduction-models-normalizations`
records the four representative tensor normalization identities.  Both node files
and their Lean modules are included in this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientNormalizedReductionCore": "4fcbe4714af552bf8e9b8df201d74a266390218f", "Sheaf.Paper.CoefficientNormalizedReductionModels": "0f3926b7a6902c5aa6c40e52908c75d72029a101", "Sheaf.Paper.CoefficientNormalizedReductionNormalizations": "d56fad9faa454b9749d4f88a439dc350a4c0e28b"}, "results": {}, "time": "2026-10-28T05:07:29+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
