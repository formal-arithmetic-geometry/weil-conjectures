## What changed

Filled `WeilConjectures.pbc_integral_pullback_identification_exists` in its own module.
The proof first identifies the completed direct-image coefficient maps by their finite
projections. An identity-on-sections right-adjoint square then gives the normalized module
comparison by adjunction uniqueness. Exactness of actual pullback and the coefficient
restriction equivalences makes ordinary pullback exact. The exact-derived square, conjugated
by the universal derived comparisons, supplies the derived isomorphism and its counit equation
on every complex. The final four-field construction preserves the published statement.
All auxiliary declarations are proved and private. Updated the item's proof plan accordingly.
The added private proof imports provide the coefficient normalization, adjunction-square
comparison, exact derived-square API, and specified universal pullback comparisons.
No public import, statement, definition, or shared module was changed.

Validation: the complete item compiled cleanly through `lcompile.py` in 30.3 seconds.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.pbc_integral_pullback_identification_exists`
(node `lem-weil-pbc-integral-pullback-identification`).
Added no holes and split off no statements. There are no remaining `sorry`s in this delivery.

## No longer needed

No original import was removed: the original statement import is still required.
The planned separate K-flat-preservation and good-complex localization argument is unnecessary:
exactness gives the derived comparison and counit normalization on all complexes.
Thus `lem-pur-integral-operations-well-defined` and
`lem-weil-pbc-ringed-topoi-derived-pullback` are not separate proof dependencies of this node.
Their existing modules are retained; they remain dependencies of the recorded constructions.
No unit statement or unit proof step is bypassed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but needlessly asks for preservation of K-flat representatives
and a new descent argument. The existing exact actual pullback and the scalar-restriction
equivalences already force exactness of ordinary pullback. Existing universal left-derived
comparison and exact-square lemmas then retain the specified counits directly.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
