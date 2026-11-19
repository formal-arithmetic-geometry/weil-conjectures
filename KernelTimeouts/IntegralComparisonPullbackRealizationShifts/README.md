# IntegralComparisonPullbackRealizationShifts

Origin: commit `b400b43ec293656136a963da2f46d2fde6d8123d` (2026-11-05), `WeilConjectures/SmoothPurity/Integral/Comparison/IntegralComparisonPullbackRealizationShifts.lean`, declaration `integralComparisonPullbackRealization_commShift`. No direct Zulip message ID was attached to the commit. The commit describes a kernel-cheap repair for a large SmoothPurity proof whose old form consumed substantial memory.

The full parent and current source files are kept as `Before.lean` and `After.lean`. With the project default heartbeat budget (200000), the old form succeeds on current 4.35.0 but takes 1:42.27 wall time, 105.11 s user CPU, and 9,386,264 KB maximum RSS. The fixed form takes 23.61 s wall time, 26.77 s user CPU, and 3,880,060 KB RSS; both exit `0`. Both reproductions explicitly set `maxHeartbeats 200000`; the original file also carries its source-level elaboration options.

The repair introduces small wrappers for a comm-shift component, a natural-transformation application, a shifted morphism, and the square equality. The localization extensionality lemma is then applied to an explicitly named composition and the wrapper types are matched syntactically. This prevents kernel weak-head reduction from unfolding derived-category shift isomorphisms and `NatTrans.app` at every concrete endpoint.

Reproduce with:

```sh
cd the master build tree
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/IntegralComparisonPullbackRealizationShifts/Before.lean
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean KernelTimeouts/IntegralComparisonPullbackRealizationShifts/After.lean
```

