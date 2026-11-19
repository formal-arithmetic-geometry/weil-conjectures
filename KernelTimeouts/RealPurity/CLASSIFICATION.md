Case ID / declaration
---------------------
RealPurity / `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`
Module: `WeilSheaf/RealPurity.lean`; origin `e2d8b540cba`
Lean / Mathlib: 4.35.0 / 4.35.0; host Weil server the build server

1. Phase attribution
--------------------
Before: kernel deterministic timeout at 58.94 s / 5,590,352 KB RSS. After:
kernel deterministic timeout at 58.84 s / 5,584,740 KB RSS. Master source:
6.10 s / 4,015,364 KB RSS, exit 0. Kernel-skipped Before/After are both about
7.4-7.8 s / 3.99 GB, so the timeout delta is trusted Kernel checking. A
per-declaration profiler attributes 52.2 s to checking the theorem at line
241; the next error is only the downstream unknown-constant cascade.

2. What is expensive?
---------------------
The Before timeout is in the value proof at the large constituent/subquotient
construction (`hσ` and its dependent equivalence); the split `as_aux_lemma`
proof still times out in the historical After. The declared theorem type is not
the source of the timeout.

3. Structural evidence
----------------------
The fixed commit moves `hσ`, `hreal'`, and the two final stalk calculations into
auxiliary proof blocks. This changes proof abstraction boundaries but leaves the
statement unchanged. Master has further changed the surrounding source and is
cheap, showing the historical fix was insufficient on 4.35.0.

4. Why is it expensive?
-----------------------
Primary B (proof-term/proof-abstraction heavy), plausible; contributing C and
A remain hypotheses. Evidence: Kernel-on versus skipped timing confirms proof
checking is expensive, while the unchanged timeout after splitting shows the
historical abstraction boundary did not remove it. The exact subterm and
mechanism need a typed-sorry bisect.

5. Confidence
-------------
Strongly supported for the Kernel phase, plausible for B, unresolved as to why
the 4.35.0 split still times out.

6. Scope and caveats
--------------------
Master.lean is the current source and passes. Before/After retain the original
historical terms and both fail as required by ROUND3.
