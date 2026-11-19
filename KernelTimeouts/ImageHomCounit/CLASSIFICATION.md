Case ID / declaration
---------------------
ImageHomCounit / `imageHomIso_counit`
Origin: `212f97dd22a`; Lean/Mathlib 4.35.0; Weil server the build server.
Imports/options: see `Before.lean`, `maxHeartbeats 200000`.

1. Phase attribution
--------------------
Synchronous Kernel on: 54.53 s / 7,458,644 KB RSS, exit 0.
Synchronous Kernel skipped: 2.90 s / 2,785,800 KB RSS, exit 0.
Baseline Before/After: 55.53 s / 2.60 s. Per-declaration profiler: type
checking 53.6 s, tactic execution 378 ms, elaboration 39.8 ms. Kernel
diagnostics count 604,574 `Functor.obj` unfolds and 842,612 `Add.add` unfolds
in this check. Conclusion: Kernel cost.

2. What is expensive?
---------------------
The target theorem value at `exact conjugateEquiv_counit` applied to concrete
global-Hom adjunctions. The declared statement is shared with the cheap After
file, so it is not the dominant cost. The expensive conversion is in checking
this application or matching its inferred result to the declaration; these
two suboperations are not yet separated.

3. Structural evidence
----------------------
Before passes concrete functor/adjunction objects directly. The fixed helper
peels their heterogeneous equality one argument at a time, ending in `rfl`.
No elaborated expression dump or `Expr.equal` comparison was retained.

4. Why is it expensive?
-----------------------
Primary E (representation/interface mismatch); contributing A and C.
The phase gate and single proof-term change support conversion over concrete
dependent arguments. Evidence strength: strongly supported.

5. Confidence
-------------
Strongly supported; a focused `HEq` pair probe could confirm the exact
cross-expression conversion.

6. Scope and caveats
--------------------
Standalone statement, current master imports; no diagnostic axiom retained.
