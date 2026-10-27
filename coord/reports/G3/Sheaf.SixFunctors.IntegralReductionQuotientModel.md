## What changed

Restored the assigned module from its preserved quarantine source and filled
`WeilConjectures.integralReductionQuotientModel` by the existing adjunction route.
The proof compares adjoint transposes, uses the specified K-flat scalar-unit
normalization at both levels, and localizes the degreewise ordinary quotient
mate equation. The eight proved private helpers isolate the ordinary chain-unit
equation, exact-localization restriction factors, abstract cancellation,
homotopy-to-complex localization of units, finite-model unit normalization,
the two equalities identifying the chosen ordinary quotient with its mate, and
the combined abstract localization calculation.
The finite-unit calculation follows the existing private calculation in
`Sheaf.Paper.CompletionUnitFiniteMateComparison`, without importing its unrelated
completion-unit theorem.

Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for the
exact-localization compositor identities. The existing public import and all
public statements remain unchanged. Updated the node's proof description and
proof origin to record the actual calculation.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.integralReductionQuotientModel`
(node `lem-coef-integral-reduction-quotient-model`).
Item holes left: zero. Holes added: zero. Split-off statements: zero.
All eight private helpers are proved. The complete module compiled cleanly in
19.5 seconds; the delivery tool performs its separate compile and axiom checks.

## No longer needed

No existing import was removed, and no module or node was withdrawn.
All three planned dependency nodes remain used through their recorded
constructions and unit normalization. The main assembly theorem
`coefficientDerivedSystemEvaluationCalculus` is not applied: this equation needs
only the canonical finite reduction, restriction and quotient constructions
already defined in its module.

## Where the brief, the DAG or earlier work was wrong

The item source was quarantined, not withdrawn. Its node, dependency structure,
and full theorem signature have been preserved. No statement correction or
change of unit route was necessary; the unit has no realized statement or steps
replaced by this proof.

LeanFinder returned general algebraic localization results, with no exact match.
Loogle found `Adjunction.homEquiv_naturality_right`. The launcher grep query found
no Mathlib statement of this project-specific equation; local searches found
the exact-localization compositor identities in the adopted source library and
the existing private finite-unit calculation described above.

The proof keeps arbitrary coefficient and scheme universes. It does not divide
by a scalar or use nonzero objects, positive n, boundedness, or flatness of terms
or of a quotient ring; n=0, zero complexes and empty schemes remain included.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
