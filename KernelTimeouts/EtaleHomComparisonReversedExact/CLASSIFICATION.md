Case ID / declaration
---------------------
EtaleHomComparisonReversedExact / `etaleHomComparison_reversedExact_commShift_component`
Module: `EtaleHomTransposeExactCommShiftComponent.lean`; origin `8ca2e912b93`
Lean / Mathlib: 4.35.0 / 4.35.0; host Weil server the build server

1. Phase attribution
--------------------
With the current instance rename (`DerivedCategory.instMonoidalCategory`), the
historical Before takes 1:50.07, 12,487,664 KB RSS and succeeds; Kernel-skipped
Before takes 3.40 s / 3,130,300 KB RSS. After takes 3.50 s / 3,196,476 KB RSS
with Kernel on and 3.30 s / 3,142,380 KB RSS skipped. A per-declaration
profiler attributes 110 s to type checking of the Before theorem. Conclusion:
strongly Kernel-dominated in the historical Before.

2. What is expensive?
---------------------
The cost is the target proof value at the `exact derivedTensorHomShiftComparison_component`
application, especially conversion of the concrete `derivedHom` endpoints.
The declared type is cheap; replacing `exact` with `have` plus `transport_exact`
removes the expensive final conversion.

3. Structural evidence
----------------------
The old and fixed expressions differ only in the transpose hypothesis transport
and the final proof handoff. The current instance spelling is a mechanical port;
the fixed form keeps the derived categories abstract until `transport_exact`.

4. Why is it expensive?
-----------------------
Primary E (representation/interface mismatch); contributing A and C. Evidence:
Kernel-on versus skipped timing, plus the controlled `have`/`transport_exact`
rewrite that preserves the statement while avoiding unfolding under `Functor.map`.
Confidence: confirmed for the current renamed port.

5. Confidence
-------------
Confirmed. A profiler-level expression diff would refine the exact hidden
instance arguments but is not needed to distinguish the mechanism.

6. Scope and caveats
--------------------
The instance rename is recorded in the case README. Kernel skipping was used
only diagnostically.
