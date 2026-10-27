## What changed

Proved `WeilConjectures.ordinaryIntegralNestedOpenRestriction` with its existing signature.
All new helpers are private and proved in the item module. The finite constant-section
normalization identifies the adjoint coefficient map; its completed counterpart follows
from uniqueness on all quotient projections. The site adjunction then identifies ordinary
module pullback with normalized exact open restriction. Uniqueness of total left derived
functors gives the derived identification. The final proof combines this with the existing
ordinary ringed pullback composition comparison twice.

Added the proof imports `Sheaf.Paper.IntegralOrdinaryPullbackComparison` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`. Updated the item's DAG proof to match the Lean argument.
No existing signature, definition, public import, or other module was changed.
Searches: LeanFinder for derived pullback composition and exact open restriction found
structure-sheaf restriction results, which do not identify these coefficient functors.
Loogle found `CategoryTheory.Functor.leftDerivedUnique`; indexed Mathlib grep found the
generic derived-functor uniqueness API. Repository search located the unrestricted
`IntegralOrdinary.pullIso` and the completed-family geometric compositor used here.

## Proved and sorry left

Closed the sole original hole, `WeilConjectures.ordinaryIntegralNestedOpenRestriction`
(node `lem-fix-ordinary-integral-nested-open-restriction`): 1 of 1 proved.
Added zero holes; no `sorry` remains in the delivery. No decomposition or new node. The coefficient, composition and assembly arguments
were separately checked by the remote compiler before consolidation into private helpers. The complete consolidated module also
compiled successfully with no remaining holes.

## No longer needed

The assigned proof does not need `lem-sf-clopen-coefficient-comparison`
(`Sheaf.Paper.SfClopenCoefficientComparison`): the published normalized open coefficients
already supply all constant-section and completed-projection equations used here.
It does not need `lem-sfb-ringed-derived-monoidal-comparisons`
(`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`): the existing ordinary ringed
composition isomorphism suffices, with no tensor or monoidal coherence data.
These two planned proof dependencies were removed from the item node. Neither was
imported by the original module. No claim is made that either module is unused by
other parents, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous search missed the unrestricted helper `IntegralOrdinary.pullIso` and the
composition comparison `PurCompactSupport.geometricPullComposition`, despite the stronger
hypotheses of the completion invertibility theorem in the same module. The helper and
composition comparison apply to all schemes and all unbounded inputs here. The completed
pullback invertibility theorem and `open_completed_restriction` are not applied.

Edge cases: the coefficient and adjunction arguments have no nonemptiness or properness
hypothesis. Identity and empty opens and zero modules use exactly the same proof.
The item's unit has no prescribed realized steps, and the unit route is preserved.
The geometric coefficient-data definitions are used as tools for their existing
completed-family compositor; the item's original monoidal-system dependency would
require additional tensor data that this plain natural-isomorphism statement does not use.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
