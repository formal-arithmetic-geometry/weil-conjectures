Case ID / declaration
---------------------
FiniteBaseChangeRestrictionMateTransport / `finite_base_change_restriction_mate_transport`
Module: `FiniteBaseChangeRestrictionMateTransport.lean`; origin `0676f555de6`
Lean / Mathlib: 4.35.0 / 4.35.0; host Weil server the build server

1. Phase attribution
--------------------
The direct historical proof placed in the current, compiling prefix with its
original 4,000,000-heartbeat scope passes in 9:37.08 / 23,906,184 KB RSS.
The fixed abstraction passes in 4.10 s / 2,322,976 KB RSS. With synchronous
Kernel checking skipped, Before passes in 4.70 s / 2,235,952 KB RSS.
The 400,000-heartbeat probe (`probes/BeforeReducedBudget.lean`) reproduces
`(kernel) deterministic timeout` in 1:28.46 / 5,731,316 KB RSS; with Kernel
checking skipped, it passes in 4.60 s. Conclusion: Kernel-dominated cost at
the historical budget and hard failure at the reduced budget. The unported
prefix first hit the changed `TwoSquare.natTrans` API; this port affects only
the prefix and theorem header.
Per-declaration profiling attributes 85.3 s to type checking of the target
declaration and 140 ms to the preceding helper check.

2. What is expensive?
---------------------
The cost site is the value of the concrete theorem application to four
equivalence records, specifically the conversion into `transport_from_unit`.
The declared theorem type and compiling prefix are shared by both forms. The
canonical Before preserves the old source's 4,000,000-heartbeat scope. The
probe changes only that scope to 400,000 to expose the hard failure on 4.35.0.

3. Structural evidence
----------------------
The old value passes concrete `mateEquiv`/equivalence fields directly to
`transport_from_unit`. The fixed value introduces `mate_transport_abstract`,
making binder domains syntactically identical before the concrete application.
The historical proof body and scoped budget are restored in canonical Before.
The reduced-budget probe changes only that budget. No `Expr.equal` or
expression-size probe was retained.

4. Why is it expensive?
-----------------------
Primary A (reduction/definitional equality); contributing C and E (dependent
transport and representation/interface mismatch). Evidence: Kernel-on versus
skipped timing, identical statement/prefix, and old direct application versus
fixed abstract helper. Confidence: strongly supported.

5. Confidence
-------------
Strongly supported. A typed argument-prefix bisect would distinguish the exact
dependent conversion from the final inferred-type reconciliation.

6. Scope and caveats
--------------------
The Before port uses the fixed source's current prefix and theorem statement
with only the historical direct proof body restored. This is a controlled
target-value probe, not an exact replay of the old module context.
