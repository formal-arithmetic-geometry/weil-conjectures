## What changed

Proved `directIntegral_reduction` in `Sheaf.Paper.SystemOperationExchangeRealization`.
Two proved private helpers calculate counit cancellation and its application to an arbitrary
system operation. The direct reduction equation specializes that calculation, without
choosing maps from finite evaluations. The naturality proof of `compactIntegral` now
normalizes only the full-subcategory wrappers; this avoids expensive conversion of the
compact-support functor. Its component maps and public signature are unchanged.

Updated the existing node's proof and proof origin; proof dependencies are unchanged.
Existing public signatures, definitions, public imports, and docstrings are preserved.

## Proved and sorry left

Closed 1 of 14 existing holes; added 0 holes; split off 0 holes:

- `WeilConjectures.FrobeniusExchange.directIntegral_reduction`.

The thirteen unchanged holes below all belong to
`def-weil-system-operation-exchange-realization` and retain their existing source and
natural-language proof docstrings:

- `WeilConjectures.FrobeniusExchange.systemDirectEvaluationOrdinary_eq`.
- `WeilConjectures.FrobeniusExchange.systemPullEvaluationOrdinaryInv_isIso`.
- `WeilConjectures.FrobeniusExchange.systemDirectEvaluation_isIso`.
- `WeilConjectures.FrobeniusExchange.systemExchange_evaluation`.
- `WeilConjectures.FrobeniusExchange.systemOpenEvaluationInv_isIso`.
- `WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso`.
- `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso`.
- `WeilConjectures.FrobeniusExchange.directImage_roos`.
- `WeilConjectures.FrobeniusExchange.directImage_linear`.
- `WeilConjectures.FrobeniusExchange.directAlpha_isIso`.
- `WeilConjectures.FrobeniusExchange.compactRealization_existsUnique`.
- `WeilConjectures.FrobeniusExchange.compactAlpha_isIso`.
- `WeilConjectures.FrobeniusExchange.compactIntegral_reduction`.

## No longer needed

None globally: no modules or existing imports are removed. The direct reduction equation
needs neither the finite-evaluation theorem nor geometric source-comparison invertibility;
those remain necessary for other declarations of this module. No unit route is bypassed.
No new intermediate statements or DAG nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

The existing prose proof suggested finite evaluation as part of proving the displayed
reduction equations. The direct equation already holds by abstract counit naturality and
inverse cancellation, before evaluation. Existing scalar-linearity helper proofs in the
compact-support modules suggested a
shorter proof of `directImage_linear`, but adding their DAG dependencies creates cycles
through the integral pullback adjunction and the item itself. That attempted route was
removed from this delivery; `directImage_linear` is unchanged. No new dependency is added.

The compact reduction equation remains its original named obligation.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
