# DefEq Cost Anatomy Report

Case: PR1556-AmbientCounterexampleCoproducts
Lean / Mathlib: Lean 4.35.0, source snapshot 1ef1fddac73
Kernel instrumentation: observational Lean 4.35.0 patch, counters and detailed-trace modes from READY-4.35.0; minimum reported root 100 ms.

Root: final congr proposition domain, Eq argument 1. Original module type checking 58.8 s, user CPU 61.40 s, RSS 7,817,824 KB. Correct replay: Quiver.Hom 1 ms, CategoryStruct.comp 48,747 ms, OfNat 0 ms. Fixed-pair control: NatTrans.app 49,048 ms, aligned 0 ms, reverse 47,020 ms.

The counters-only slow root 826 took 77.188 s: 6,670,198 recursive calls, maximum depth 213, 39.404 s exclusive comparison (51.0%) and 37.784 s exclusive reduction (49.0%). It made 22,063,668 WHNF requests and 13,242,067 Delta unfolds; Delta itself took 1.362 s. The second slow root 3655 had a nearly identical 77.645 s / 6,668,281-call profile, but the two are separate replay conversions and must not be added as parent/child cost.

Diagnostics showed Add.add 38,416 and Functor.obj 26,790 unfolds in the original module; these counts are not time. Proposition timer values overlap nested work, so proof-type cost is not separately attributable. Counters mode has no pair identities; trace supplies the bounded pair study. No allocation/GC counters exist, and counters peak RSS was 16,826,556 KB versus 7,817,824 KB release.

The generated congr proposition's CategoryStruct.comp/NatTrans.app comparison is the dominant measured child. Its internal workload is mixed (outcome F), deep, and approximately half comparison/half reduction.

Detailed root 826 reproduced 6,670,198 calls and depth 213 in 95.643 s. The bounded 5,000,000-call pair sample had 3,428,653 distinct exact pairs, 1,571,347 repeated entries, and 2,615,405 structural groups; repeat entries contributed 565 ms exclusive comparison time. Top exclusive children were SMul.smul (528 ms), HAdd.hAdd (502 ms), Eq (251 ms), and AddCommGroup.proj (228 ms). No single leaf accounts for the parent. The exact-pair key omits local-context identity and the pair sample is bounded.

Aligned source counters had no 77 s root; the largest remaining root was 3.264 s with 284,842 calls. Both reduction and comparison work associated with the hot proposition disappear, while other module work remains. Detailed trace peak RSS was 17,740,680 KB, confirming substantial instrumentation memory overhead.

## Reproducibility and cost accounting

Root ID 826 is a slow Kernel conversion in the replay of the final congruence proposition. The release argument replay identifies `Eq` argument 1 as the two `CategoryStruct.comp` expressions containing the differing `NatTrans.app` major premises; the trace does not print a full root left/right expression to establish an exact ID-to-argument mapping. The exact elaborated expressions and dependent context are preserved by `probes/anatomy/replay/WeilConjectures/SixFunctors/ProEtale/AmbientCounterexampleCoproducts.lean`; the in-situ source and aligned source are in neighboring `original/` and `aligned/` directories. The root counters, trace and aligned counters artifacts are named `*.root-counters.metrics.txt`, `*.trace.metrics.txt`, and `*.aligned-counters.metrics.txt` beside those sources. The trace artifact contains the ranked 20 child calls and full depth/fan-out histograms; maximum fan-out across its roots is 21.

Trace root 826 made 22,063,668 WHNF requests (42.864 s), 13,242,067 Delta unfolds (1.491 s), 13,118,164 Beta steps, 3,154 Iota steps, 365,155 Zeta steps and 2,192,858 projections. It recorded 276,829 Pi-domain comparisons, 126,864 proposition comparisons and 3,352,429 proof attempts. The proposition timer (296.407 s) overlaps nested comparisons; it is not an exclusive proof-type cost. These counts show substantial dependent/proof work, but the kernel patch does not isolate its share of the 52.778 s trace comparison timer. Pair capture stops at five million calls, and its key omits local context. No allocation, live-heap or GC timer was available. The aligned source eliminates the slow root and lowers both call count and reduction work at this site; other module conversions remain.
