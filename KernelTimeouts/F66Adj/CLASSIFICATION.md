Case ID / declaration
---------------------
F66Adj / `imageHomIso_naturality`
Origin: `f66ad18a9ed`; Lean/Mathlib 4.35.0; Weil server the build server.
Imports/options: see `Before.lean`; parent scopes `maxHeartbeats 400000`, fixed
uses default 200000.

1. Phase attribution
--------------------
Synchronous Kernel skipped: Before 4.30 s / 2,801,496 KB RSS; After 3.60 s /
2,796,036 KB RSS. Baseline Kernel-on: Before 1:56.47 / 12,639,544 KB RSS;
After 3.40 s / 2,835,572 KB RSS. Conclusion: Kernel-dominated cost.
Per-declaration profiling attributes 117 s to type checking of the slow
declaration, versus 1.43 s cumulative elaboration and 113 ms tactic execution.

2. What is expensive?
---------------------
The target proof value applying the abstract naturality/counit helper with
concrete coefficient variance and restriction comparison. The near-equal
skipped timings show the type and elaboration are not the large cost. The
specific application argument conversion remains unisolated.

3. Structural evidence
----------------------
The fixed helper binds the target coefficient variance `γ` explicitly and
substitutes its equality. This makes the `NatTrans.app` argument structurally
match the expected domain. Exact hidden instance terms were not dumped.

4. Why is it expensive?
-----------------------
Primary E; contributing A and C. Controlled source diff plus phase gate
support a concrete interface/instance mismatch causing reduction through
derived functors. Evidence strength: strongly supported.

5. Confidence
-------------
Strongly supported; binder-aware expression diff would confirm the minimal
implicit argument mismatch.

6. Scope and caveats
--------------------
Standalone historical module; baseline timings compare different heartbeat
budgets, but both succeed and the skip control isolates Kernel cost.
