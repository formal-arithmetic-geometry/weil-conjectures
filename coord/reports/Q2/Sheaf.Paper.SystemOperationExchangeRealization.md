## What changed

Proved `WeilConjectures.FrobeniusExchange.compactAlpha_isIso` in
`Sheaf.Paper.SystemOperationExchangeRealization` from the existing normalized compact
realization. Its projection equation identifies each finite evaluation of the operation
counit, up to three isomorphisms, with the finite compact-support reduction isomorphism.
Cancel those isomorphisms and apply joint conservativity of finite derived evaluation.
Pullback and inverse limit preserve this counit isomorphism, proving invertibility of
exactly the already defined compact alpha composite.

Updated the item's DAG proof, proof dependencies and proof origin to record this argument.
No statement, definition, public import, attribute, or unit route changed. No new imports.

Validation: `lcompile.py` compiled the complete item successfully in 56.3 seconds.
The item produced no warnings. Static checks found eight remaining `sorry` tokens and
no line longer than 100 characters.

## Proved and sorry left

Closed one of the nine existing holes:
`WeilConjectures.FrobeniusExchange.compactAlpha_isIso`.
Added zero holes and zero split-off statements.

Eight existing holes remain, all attached to
`def-weil-system-operation-exchange-realization`:

- `WeilConjectures.FrobeniusExchange.systemDirectEvaluation_isIso`
- `WeilConjectures.FrobeniusExchange.systemExchange_evaluation`
- `WeilConjectures.FrobeniusExchange.systemOpenEvaluationInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso`
- `WeilConjectures.FrobeniusExchange.directImage_roos`
- `WeilConjectures.FrobeniusExchange.directAlpha_isIso`
- `WeilConjectures.FrobeniusExchange.compactRealization_existsUnique`

## No longer needed

None. No import, node or module is withdrawn. The normalized compact-realization theorem
and its evaluation mates remain needed; this proof uses their existing statements.
The compact alpha obligation needs no additional preservation or resolution theorem
beyond the existing compact projection normalization and system conservativity.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition defect found. The existing compact-realization
normalization already supplies the finite counit equations needed for compact alpha.
It is therefore unnecessary to repeat the geometric resolution and cartesian-system
argument described in that obligation's docstring.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
