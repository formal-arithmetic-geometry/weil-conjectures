## What changed

Added the finite-level comparison data module and the strict-tower assembly module. The assigned theorem now obtains finite-level data and applies the assembly theorem, with proof-only imports for both helpers.

## Proved and sorry left

`openQuotientScalarComparisonExistence` is proved by composing the two named helper theorems. The new declarations `openQuotientScalarComparisonLevelData` and `openQuotientScalarComparisonAssembly` retain one `sorry` each, recorded by nodes `lem-sf-open-quotient-scalar-comparison-level-data` and `lem-sf-open-quotient-scalar-comparison-assembly`.

## No longer needed

No imports or declared dependencies were pruned; the original data definition remains the sole public dependency of the assigned module.

## Where the brief, the DAG or earlier work was wrong

The original node treated degreewise construction and strict-tower assembly as one opaque proof obligation. They are separate strictly simpler steps: finite-level normalized maps with successor transition coherence, followed by their `NatIso.ofComponents` assembly. No target statement was changed.

## New nodes

`lem-sf-open-quotient-scalar-comparison-level-data` records the finite-level normalized family and transition coherence. `lem-sf-open-quotient-scalar-comparison-assembly` records the strict tower assembly from that family.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarComparisonAssembly": "4dbcca8a005902a94fd1065377ba954317f0bedc", "Sheaf.SixFunctors.OpenQuotientScalarComparisonExistence": "ce933dfed0f9ff0e493da5da797a1dc8c7f3e611", "Sheaf.SixFunctors.OpenQuotientScalarComparisonLevelData": "98c07163c86ddd83ba44de3816d31c13685d3386"}, "results": {}, "time": "2026-10-28T04:29:19+0800", "transitive": 0, "version": 1}
```

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
