# DefEq Internal Cost Experiments

Case: `PR2122-DiagonalTraceFiniteEtaleIntegralBoundary`
Lean / Mathlib: Lean 4.35.0, snapshot `1ef1fddac73`

## A1: original recursor context

Root: value checking inside the original dependent `Exists.casesOn`, with 14
binders and 12 lets. The selected counters root was 2,227,198 calls, depth
93, 25.836 s wall, split into 11.486 s comparison and 14.349 s reduction.
The detailed root was 32.456 s with 16.796/15.660 s comparison/reduction. It
made 7,371,950 WHNF requests (15.660 s), 4,473,309 Delta unfolds (667 ms),
60,324 Pi-domain comparisons, 34,383 proposition comparisons, and 1,190,293
proof attempts; there were no Iota steps. Pair capture found 1,535,674
distinct exact pairs and 691,524 repeats; repeats contributed 287 ms (1.7%)
of comparison-exclusive time. The largest listed child was `AddCommGroup.proj`
(236 ms), followed by `ModuleCat.carrier` (113 ms), `HAdd.hAdd` (55 ms), and
`Functor.obj` (26 ms), so no single child accounts for the root.

## C: branch-local dependent comparison

The original-context branch audit measured the motive at 16,115 ms and the
stored witness/predicate branch at 18,419 ms (body 2,212 ms). The final
dependent branch cannot be checked independently: its expected type is
provided by the recursor motive, and replacement attempts fail type checking.
This is a validity failure, not an unmeasured timeout. Consequently no
position-level proposition attribution or isolated binder-instantiation
claim is made. The aligned split module's largest root was 5.142 s / 510,125
calls, but it changes module boundaries and is only a statement-level control.

## A/B status and accounting

No same-consumer type-preserving A2 or shared-provider B variant exists in the
original branch. Concrete category/functor candidates remain hypotheses, not
measured causes. `probes/ad/profile.txt` records the branch checks, original
trace, and aligned control. Proposition timers are nested; allocation/GC
counters were unavailable.
