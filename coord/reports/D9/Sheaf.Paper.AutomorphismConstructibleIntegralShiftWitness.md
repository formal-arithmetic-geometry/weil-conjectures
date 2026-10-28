## What changed

Proved `WeilConjectures.automorphismConstructibleStage_integral_shift_witness` in
`Sheaf.Paper.AutomorphismConstructibleIntegralShiftWitness`, with its statement unchanged.
The private helpers construct the full-subcategory shift, prove its component normalization,
transfer triangulatedness through the normalized realization, and prove compatibility of the
specified composition comparison. The final proof pastes the two composition comparisons
with equality transport and uses the prescribed component formula to identify this paste with
`b`.

Added proof-only imports of `AutomorphismConstructibleIntegralShiftData`,
`IntegralComparisonPullbackRealizationShifts`, and the existing derived exact-functor shift
API `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`. Updated the item's
DAG proof and dependencies to describe this route. No existing public declaration changed. The complete proof compiled in 49.6 seconds
with profiling enabled; profiling options were removed for delivery.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.automorphismConstructibleStage_integral_shift_witness`
(node `new-h2-integral-shift-witness`). The delivered module has zero `sorry` declarations;
zero new holes and zero split-off statements are added. Every private helper is proved.

The proof uses the existing, separately assigned statements
`WeilConjectures.automorphismConstructibleStage_integral_shift_data`
(node `new-h2-integral-shift-data`) and
`WeilConjectures.integralComparisonPullbackRealization_commShift`
(node `lem-sf-integral-pullback-realization-shifts`). Their existing holes are neither moved
nor changed in this delivery.

## No longer needed

No imports are removed, and no DAG nodes or modules are withdrawn. The original public
imports supply the public statement vocabulary and inherited constructible triangulation. The original node had no listed proof dependencies
to prune. The proof needs no new finite-level or Roos-coordinate sublemmas: the existing
normalized realization compatibility theorem provides that part of the argument.

## Where the brief, the DAG or earlier work was wrong

The original single proof step did not specify the descent of the prescribed composition
comparison. The updated proof records the actual paste: realization, the invertible
reduction counit on constructible objects, derived sequence composition, and inverse
realization. Exact-functor shift compatibility and faithful inclusion then give the result.
There is no statement defect or change to the unit route. The choice of shifts is made once
as a family over all maps, so equality transport along the commuting square preserves the
chosen shifts by equality induction.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AutomorphismConstructibleIntegralShiftWitness": "feebb0f8ea074c61f88249d7edfaabd01bb53093"}, "results": {"Sheaf.Paper.AutomorphismConstructibleStageEquivalence": {"hash": "96d5edca7d4a1fab66ad0d460a4ebbddef48da06", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T10:31:04+0800", "transitive": 0, "version": 1}
```

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
