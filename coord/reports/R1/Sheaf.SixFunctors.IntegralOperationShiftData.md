## What changed

Closed `IndependentExpression.reductionContext_evaluate` by combining the existing
`IndependentExpression.variableContext_evaluate` identity with a proved pointwise
update lemma for the product of reduction functors. Added one private helper,
`pi_obj_update`, and retained the existing public imports.

## Proved and sorry left

Proved: `IndependentExpression.reductionContext_evaluate`.

Sorries left, unchanged: `tensorShifts_existsUnique`,
`IndependentExpression.shift_naturality`, and `limitShift_roos`.

## No longer needed

None. The existing imports remain required by the declarations and the proof.

## Where the brief, the DAG or earlier work was wrong

None identified.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
