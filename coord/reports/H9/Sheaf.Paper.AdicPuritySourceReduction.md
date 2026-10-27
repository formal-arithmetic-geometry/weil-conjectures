## What changed

Proved WeilConjectures.purAdicReductionShift_existsUnique in
Sheaf.Paper.AdicPuritySourceReduction. A proved private generic lemma constructs the
comparison of two shifted right Kan extensions and proves uniqueness from the counit
factorization equation. The concrete theorem uses the existing scalar-reduction universal
and pointwise witnesses. Added a private proof import of
Mathlib.CategoryTheory.Functor.KanExtension.Preserves.

Public signatures, public imports, docstrings and definition bodies remain verbatim.
Local irreducibility boundaries prevent expansion of scalarReductionExistence,
scalarReductionDerivedExistence, HasDerivedCategory.standard and
SheafOfModules.monoidalCategory. Change record:
coord/changes/H9-adic-source-comparison-proof-scope.md.
Updated def-pur-adic-source-reduction with the implemented proof and remaining obligation.
Single-file lcompile.py validation compiled the delivered text in 34.6 seconds.

## Proved and sorry left

Closed WeilConjectures.purAdicReductionShift_existsUnique:
1 of 2 original holes closed; no new holes or split-off statements.
Remaining original hole: WeilConjectures.purAdicFiniteSourceIdentification_existsUnique
(node def-pur-adic-source-reduction). Its original statement and complete proof docstring
are unchanged. No other sorry remains in the module.

## No longer needed

None. Both original public imports and all three statement dependencies remain needed.
No node or module is withdrawn; the unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The definition node had no numbered proof plan despite containing two normalization
existence-and-uniqueness theorems. The existing docstrings supplied the construction.
The finite-source proof draft reaches the generic uniqueness argument, but identifying
its concrete endpoint with the source of the finite purity arrow caused expensive
unfolding. The generic model helper compiled separately, but the full specialization
is not delivered as a proof. Its last diagnostic compile was stopped by the compiler
host reporting no space left on device when creating a temporary directory.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
