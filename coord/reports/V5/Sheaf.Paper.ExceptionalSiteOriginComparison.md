## What changed

Completed `AlgebraicGeometry.exceptionalSiteOriginComparison` by assembling a core site-comparison construction with the finite inverse lower-bound and evaluation lower-bound components. Added `ExceptionalSiteOriginComparisonCore.lean` containing the three strictly smaller source-level obligations used by the assembly, and updated the item node to record this proof route.

## Proved and sorry left

The item theorem `AlgebraicGeometry.exceptionalSiteOriginComparison` is proved (one item-level `sorry` closed). Three strictly smaller obligations remain as named theorem statements in `Sheaf.Paper.ExceptionalSiteOriginComparisonCore`:

- `AlgebraicGeometry.exceptionalSiteOriginComparison_evaluation_bound` (evaluation preserves `IsGE` bounds);
- `AlgebraicGeometry.exceptionalSiteOriginComparison_level_inverse_bound` (finite inverse preserves `IsGE` bounds);
- `AlgebraicGeometry.exceptionalSiteOriginComparison_core` (core comparison construction and levelwise unit/counit assertions).

Thus three sorries were split off.

## No longer needed

None. The core node retains the original comparison, finite-adjunction, and evaluation proof dependencies; the item proof uses all three new nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier single proof step combined the geometric construction, finite-level boundedness, and evaluation-origin projection into one obligation. Those interfaces are independent in Lean, so the route is recorded as three strictly smaller theorem statements and a concrete assembly proof. No target statement or definition was changed.

## New nodes

- `lem-sf-exceptional-site-origin-comparison-bound`
- `lem-sf-exceptional-site-origin-comparison-level-bound`
- `lem-sf-exceptional-site-origin-comparison-core`

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalSiteOriginComparison": "f3ed4c96d9bf6e76f735400732ddacf888e82c10", "Sheaf.Paper.ExceptionalSiteOriginComparisonCore": "fe870f5bc4c94f021b62ee1f9d6a1c6f7fa8f87a"}, "results": {"Sheaf.Paper.ExceptionalSystemTransport": {"hash": "5c64defc13e63e8cf084e585bdb77528a7b5bbc7", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralSystemExistence": {"hash": "3a2762881292a445abf50cc8f61fb3b3c0be90cb", "status": "OK"}}, "seconds": 55, "time": "2026-10-28T01:38:04+0800", "transitive": 0, "version": 1}
```

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
