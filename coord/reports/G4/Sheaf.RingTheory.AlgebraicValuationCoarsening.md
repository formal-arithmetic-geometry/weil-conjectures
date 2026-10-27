## What changed

Proved `ValuationSubring.algebraic_coarsening_correspondence` in
`Sheaf.RingTheory.AlgebraicValuationCoarsening`, preserving its signature and all
public imports. Added a private, explicit fraction-subring construction and proved
its restriction formula. The existing proved power-times-unit theorem yields both
the value-group assertion and reflection of inclusion of overrings. Restriction is
surjective by the fraction construction, giving the required order isomorphism;
its injectivity proves the top equivalence and proper lifting.

The only added proof import is `Mathlib.RingTheory.Algebraic.Integral`, supplying
the algebraicity instance for a finite-dimensional extension. The existing
`Sheaf.RingTheory.ValuationValueGroupTorsion` import is used. Updated proof steps
5–6 and proof origin in the item's node to record the positive-root argument.
No existing statement, definition, attribute or public import was changed.

Validation: `lcompile.py` compiled the complete proof with exit code 0, no
warnings, in 4.1 seconds. Delivery runs the final compile and preflight checks.

## Proved and sorry left

Closed 1 of 1 holes: `ValuationSubring.algebraic_coarsening_correspondence`
(node `lem-per-algebraic-valuation-coarsening-correspondence`).
Added 0 holes. No `sorry` remains in the delivered module. Every private helper is
proved, and the fraction subring has concrete data and proved closure fields.

## No longer needed

No original import, dependency node, or module is removed. All declared proof
dependencies remain used. The original explicit fraction calculation proving
uniqueness is replaced by the shorter positive-root argument using the same
power-times-unit declaration. The blueprint unit's route is preserved.

Temporary unused tactic imports were removed before validation.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The existing DAG proof is valid; its uniqueness
step admits the shorter argument now recorded in the node. The cases of a zero
numerator, a zero base element, the trivial valuation, top overrings, and positive
exponents are handled explicitly or by the ordered value-group lemmas. The lift's
denominators are required nonzero, and its construction uses no arbitrary witness
from an unproved existence theorem.

Files touched: the item module and its node, plus this report. No scratch files or
other existing modules were changed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
