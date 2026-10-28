## What changed

Proved `WeilConjectures.podIntegralHomComparison_naturality` by the prescribed
inverse-transpose argument. Private, fully proved helpers establish ambient
evaluation dinaturality, transpose normalization, naturality of the completed
tensor unit, and integral inverse-transpose and evaluation naturality. The final
calculation uses naturality of the inverse pullback-tensor isomorphism.

The public statement and imports are unchanged. The node proof now records the
formal argument. No other existing module is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.podIntegralHomComparison_naturality`.
There are zero remaining holes in this module and zero holes added or split off.
Every private helper is proved. The module compiled successfully in 13.4 seconds
with no warnings, using the prescribed remote compiler. Existing imported
statements retain their own proof obligations.

## No longer needed

None. No imports, modules, or declared proof dependencies were pruned. No new
modules or nodes are required.

## Where the brief, the DAG or earlier work was wrong

No statement repair or change of mathematical route was needed. Pair naturality
is established from the prescribed completion-unit normalization and the ambient
adjunction, rather than assumed as a field of the partial closed interface.
Related calculations in downstream modules are private; local proved helpers
avoid an import cycle and preserve the existing public interface.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodIntegralHomComparisonNaturality": "a7b4f373b732213cc91e21e260a52bed5eba8348"}, "results": {"Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA": {"hash": "2e9552db49b2b434602492555058e2dfefccf892", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T10:13:34+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
