## What changed

Proved `WeilConjectures.StrictQuotient.strictUnitOrdinaryAdjoint` in
`Sheaf.Paper.StrictUnitOrdinaryAdjoint`, preserving its complete signature and existing
public import. Added the private proof import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` and private proved helpers.
The proof identifies evaluation of the strict module unit, verifies the actual horizontal
transition on one using `coefficientSequenceTransition_exists`, and detects invertibility
of the scalar adjunct through the global-section Hom bijection. It then lifts this result
to the degree-zero complex, using zero objects in every other degree. Updated the item's
DAG proof to record this route and its explicit ringed-sequence-site dependency.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.StrictQuotient.strictUnitOrdinaryAdjoint`
(node `lem-pur-strict-unit-ordinary-adjoint`).
No holes added; no `sorry` remains in the delivered module. All private helpers are proved.
The final module compiled with `lcompile.py` in 45.7 seconds, exit code 0.
The original theorem signature is preserved verbatim; no development options remain.

## No longer needed

No original import, node, or module is pruned. Both original proof dependencies remain;
`def-coef-ringed-sequence-site` is now recorded explicitly because its actual transition
section formula is used. The direct Hom-bijection argument replaces the planned explicit balanced-tensor inverse.

## Where the brief, the DAG or earlier work was wrong

The original mathematical statement is unchanged and true. The DAG's explicit tensor
inverse and appeal to `D.ordinary_unit` are unnecessary for invertibility: the unit
adjunct is invertible for every adjunction with the prescribed scalar restriction, by
coyoneda and `unitHomEquiv`. The argument allows equal levels, zero rings and the empty
scheme, and uses no flatness of the quotient. The blueprint unit route is preserved
(the unit record has no realized steps bypassed by this proof).

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
