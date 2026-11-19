Case ID / declaration
---------------------
IntegralComparisonPullbackRealizationShifts / `integralComparisonPullbackRealization_commShift`
Origin: `b400b43ec29`; Lean/Mathlib 4.35.0; Weil server the build server.
Imports/options: see `Before.lean`, `maxHeartbeats 200000`.

1. Phase attribution
--------------------
Kernel skipped, synchronous: Before 11.11 s / 2,744,228 KB RSS; After
10.61 s / 2,745,456 KB RSS, both exit 0. Baseline Kernel-on Before 1:42.27 /
9,386,264 KB RSS; After 23.61 s / 3,880,060 KB RSS. This is a strong Kernel
gate for the cost difference, though whole-file elaboration contributes about
11 s in both variants. Per-declaration profiling attributes 95.2 s to type
checking of the slow declaration (the earlier declarations have checks of
2.9 s or less), with 6.01 s cumulative tactic execution in the file.

2. What is expensive?
---------------------
The target proof value around the localization extensionality application and
the `CommShift` endpoint conversion. Wrapper definitions in the fixed form
preserve the theorem statement while reducing the concrete conversion. The
exact application prefix and final reconciliation have not been timed apart.

3. Structural evidence
----------------------
The fixed term names the comm-shift component, natural transformation app,
shifted morphism, and square equality. That makes endpoint types syntactically
match before localization. The per-declaration profiler identifies the target
as the 95.2 s type check in the full source.

4. Why is it expensive?
-----------------------
Primary A; contributing E and C. Kernel skipping removes the large delta;
the wrapper change points to reduction under dependent localization endpoints.
Evidence strength: strongly supported for phase, plausible for exact mechanism.

5. Confidence
-------------
Plausible site, strongly supported phase. Per-declaration profiler and a
typed-sorry bisect would raise the site attribution.

6. Scope and caveats
--------------------
Whole historical module measurement, not an isolated target-only probe.
