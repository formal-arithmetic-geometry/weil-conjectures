## What changed

Added `Sheaf.SixFunctors.OpenQuotientScalarComparisonCanonicalTransition`, defining the
concrete canonical finite-level comparison and splitting its successor-square generator
calculation into `openQuotientScalarComparisonCanonicalTransition`. The assigned theorem
now rewrites arbitrary level components with its `components` hypothesis and applies that
canonical square. The assigned module imports the new proof-only module.

## Proved and sorry left

The assigned theorem `openQuotientScalarComparisonTransition` is proved from the
component equations and the canonical square. One sorry remains in the newly added
`openQuotientScalarComparisonCanonicalTransition` theorem, node
`lem-sf-open-quotient-scalar-comparison-canonical-transition`; it is the pure-tensor
successor calculation described in its docstring. No sorry occurs in the canonical level
definition.

## No longer needed

No imports or declared dependencies were pruned. The original data dependency remains
needed for the canonical comparison construction.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan hid the nontrivial pure-tensor calculation. The arbitrary
level family is determined only through its component equations, so the proof naturally
reduces to the concrete canonical level square. That square is now a separate, strictly
simpler node with no arbitrary level family or component premise. No target statement or
existing definition was changed.

## New nodes

`lem-sf-open-quotient-scalar-comparison-canonical-transition` records the canonical
pure-tensor successor square and is stated in
`Sheaf.SixFunctors.OpenQuotientScalarComparisonCanonicalTransition`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarComparisonCanonicalTransition": "445cb141fd95eb5d73cba846ef513f31ec6c043f", "Sheaf.SixFunctors.OpenQuotientScalarComparisonTransition": "c35bfbae67deabf145184e3d3536310b1e1ff728"}, "results": {}, "time": "2026-10-28T09:24:38+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
