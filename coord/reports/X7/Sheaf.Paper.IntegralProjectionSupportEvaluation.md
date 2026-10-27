## What changed

Proved `WeilConjectures.IntegralProjectionReduction.integralProjectionSupportEvaluation`
in `Sheaf.Paper.IntegralProjectionSupportEvaluation`, with its statement unchanged.
Added a proof-only import of `Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates`.
Its proved theorem gives the same unary support adjunct equation before the final
finite-support realization is cancelled. Postcomposition with that realization's
inverse, associativity, and the isomorphism cancellation identity give the result.
Updated the item's DAG proof and proof dependencies to this route. No public
interfaces, shared definitions, or other modules changed.

Validation: the required server single-file compile passed cleanly in 8.3 seconds.

The module search found the existing finite-coordinate theorem, and the import
cycle check permits its use. LeanFinder returned only unrelated finite-support
function results. Loogle did not resolve the unqualified generated cancellation
lemma; the grep search found its use throughout Mathlib's category theory files.
Both nodes belong to `sk-rem-sf-pf-done`, whose unit record has no prescribed steps
that this reuse would bypass.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.IntegralProjectionReduction.integralProjectionSupportEvaluation`
(node `lem-sf-integral-projection-support-evaluation`).
The item has 0 remaining holes. Added 0 holes and split off 0 statements.
The existing finite-coordinate theorem has a complete proof; its own dependencies
are reused without alteration.

## No longer needed

No existing imports were removed, and no module is withdrawn. The original direct
proof plan's dependencies `lem-coef-derived-system-evaluation-calculus`,
`lem-sf-integral-support-counit-projection`,
`def-sf-integral-projection-coordinate-data`, and `def-fix-six-functor-datum`
are not separately used as proof dependencies of this item. The finite-coordinate
theorem already performs the normalization calculation. The calculus and coordinate
definitions remain transitively needed, so this delivery does not claim that their
modules are globally prunable. In particular, the support-counit-projection theorem
is not imported for this proof.

## Where the brief, the DAG or earlier work was wrong

The DAG plan missed the existing
`WeilConjectures.FixProjectionCompactification.integralSupportAdjunctFiniteCoordinates`.
Its conclusion is precisely the equation needed before cancelling finiteSupport.
This permits closing the item directly instead of repeating or splitting the
normalization argument. There is no mathematical statement correction and no new
assumption. The proof is uniform in the quotient level, including m = 0, zero
inputs and empty opens, since it only uses that theorem and isomorphism identities.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
