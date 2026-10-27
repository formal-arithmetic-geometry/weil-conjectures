## What changed

Proved `WeilConjectures.compactSupportCompletedRestrictionTransition` in
`Sheaf.TraceFormula.CompactSupportCompletedRestrictionTransition`, preserving its signature.
The ordinary square follows from the actual sectionwise characterizations of coefficient
restriction and quotient transitions, together with the completed limit-cone equation.
A proved private localization square passes this equality to all unbounded derived objects.
The argument adapts the existing private proof in `Sheaf.Paper.CoefficientSequenceRoosModel`
to `eqToIso (coefficientRestrictionComp ...)`, without the auxiliary finite-field datum.
Kept scalar-composition comparison behind a private canonical isomorphism and proved
its equality to the specified equality isomorphism, avoiding expensive kernel conversions.
Enabled respect for transparency in the coefficient calculations.
Added proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for the
composition comparison and its factorization lemmas.
Updated the item's node proof to record both steps and its use of the already proved
`coefficientRestrictionComp` from the evaluation calculus.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.compactSupportCompletedRestrictionTransition`
(node `lem-trf-completed-restriction-transition`).
No holes added; no `sorry` remains in the delivered module. All private helpers are proved.
The delivery compiler checked the complete proof in 17.4 seconds; its remaining line-width
warning was corrected before resubmission.

## No longer needed

None of the assigned proof dependencies is pruned. No imports removed.
The auxiliary finite-field datum, normalization of the input system, K-injective
representatives and Roos-limit theory used elsewhere in `CoefficientSequenceRoosModel`
are unnecessary for this compatibility, so that module is not imported.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The proposed argument is correct. Its explicit use of the existing
`coefficientRestrictionComp` was missing from the recorded proof dependencies;
the node now records `lem-coef-derived-system-evaluation-calculus` as well.
There are no changes to shared definitions, existing signatures or the unit route.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
