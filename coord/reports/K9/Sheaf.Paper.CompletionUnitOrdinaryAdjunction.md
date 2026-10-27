## What changed

Replace the hole in `WeilConjectures.CompletionUnit.ordinaryModel_exists` with a proof
from the existing `purSequenceOrdinaryFactorization`. Add its module as a private proof
import. Its ordinary data supplies the additive tensor, finite evaluation comparisons
and every quotient-transition equation. Transport its adjunction through the recorded
limit isomorphism. Applying its coordinate transpose formula to the adjunction unit,
then cancelling the finite tensor comparison, proves the prescribed unit formula.
Construct the comparison for limits of complexes from the degreewise universal cones
and prove its projection equation. All auxiliary declarations are private and proved.

The existing theorem signature, public import and docstring are preserved. No existing
definition, consumer, target or blueprint unit is changed. Update only the existing
node's proof, proof dependencies and proof origin to describe this route.

Validation: the final item module compiled cleanly through `lcompile.py` in 13.8 seconds,
with no warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.CompletionUnit.ordinaryModel_exists`
(node `lem-trf-completion-unit-ordinary-adjunction`).

Holes added: 0. Holes left in the delivered module: 0. No split-off statement.
The proof uses the existing, still unfinished
`WeilConjectures.purSequenceOrdinaryFactorization`
(node `lem-pur-sequence-ordinary-factorization`); that theorem is not changed here.

## No longer needed

No original Lean import is removed and no module is withdrawn. The direct dependencies
`lem-coef-sequence-projection-derived-adjunction` and
`lem-pur-system-ringed-sequence-site`, and the explicit construction through
`def-coef-ringed-sequence-site`, are unnecessary in this item's proof: the existing
ordinary factorization already packages those constructions. They remain dependencies
of that existing theorem or of the statement interface, so this delivery claims no
module pruned from the target closure. The initially explored generator argument and
`Sheaf.CategoryTheory.SystemScalarGenerators` are not imported by the final proof.

## Where the brief, the DAG or earlier work was wrong

The planned direct construction duplicates the ordinary part already stated in
`purSequenceOrdinaryFactorization`. Its stronger interface has exactly the tensor
transition equations and coordinate transpose normalization needed here. The only
additional arguments are the projected-unit cancellation, the existing scalar tensor
normalization, and degreewise limits of complexes. Checked that neither its Lean
imports nor its DAG dependencies return to this item. No mathematical defect or
statement repair was needed; site and coefficient universes remain independent.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
