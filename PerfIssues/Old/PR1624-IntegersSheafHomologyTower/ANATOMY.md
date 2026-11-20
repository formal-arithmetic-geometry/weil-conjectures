# DefEq Cost Anatomy Report

Case: PR1624-IntegersSheafHomologyTower
Lean / Mathlib: Lean 4.35.0, source snapshot 1ef1fddac73
Kernel instrumentation: observational Lean 4.35.0 patch, counters and detailed-trace modes from READY-4.35.0; minimum reported root 100 ms.

Root: final Iso.trans dependent endpoint domain. Original target type checking 104 s; CPU 114.09 s; wall 115.21 s; RSS 11,070,104 KB. Correct replay endpoint Functor.comp children were 14,769 ms and 29,112 ms; carrier/category 0 ms. Aligned target check 3.42 s; RSS 2,691,600 KB.

Two counters-only replay roots each took about 76.8 s with 6,598,5xx recursive calls and depth 88. Root 22078 split into 38.767 s exclusive comparison (50.5%) and 37.985 s reduction (49.5%). A further nested root took 34.834 s with 3,302,864 calls and depth 106. These roots arise from separate replay operations and cannot be summed as one parent tree. Counters peak RSS was 22,157,028 KB versus 11,070,104 KB release; allocation/GC counters were unavailable. Proposition timings overlap nested work.

Two dependent endpoint comparisons carry the release cost. Internal cost is mixed (outcome F), near equal comparison and reduction, with substantial depth.

Detailed root 22078 took 89.713 s with 6,598,545 calls and depth 88. Of the first 5,000,000 calls captured, 3,361,091 exact pairs were distinct, 1,638,909 were repeats, and 2,605,442 structural groups were found; repeated entries contributed 672 ms exclusive comparison time. Its top exclusive children were Add.add (24 ms), NSMul.nsmul (24 ms), LinearMap.mk (12 ms), and a LinearMap proof field (11 ms). Cost is widely distributed across small children; the pair capture omits local context and is bounded.

The aligned source counters reduced the largest root to 5.256 s and 456,393 calls, with 2.557 s exclusive comparison and 2.700 s reduction. Both categories and call count fell sharply. Trace peak RSS was 23,104,824 KB, versus 11,070,104 KB for release.

## Reproducibility and cost accounting

Root ID 22078 occurs in the valid original `Iso.trans` target replay under `probes/anatomy/replay/WeilConjectures/SixFunctors/ProEtale/Adic/IntegersSheafHomologyTower.lean`. The complete dependent telescope, including both `Functor.comp` endpoints, is preserved there and in the original module; the aligned source is in `aligned/`. The release endpoint replays give 14.769/29.112 s, while carrier and category arguments take under 1 ms. Thus the full endpoint conversion enters work absent from the cheap isolated arguments. The replay `*.root-counters.metrics.txt` and `*.trace.metrics.txt` contain all root summaries, ranked 20 child comparisons and depth/fan-out buckets; maximum fan-out across trace roots is 21. The aligned `*.aligned-counters.metrics.txt` provides the control profile.

Trace root 22078 made 21,908,916 WHNF requests (40.275 s), 12,966,166 Delta unfolds (1.398 s), 12,865,920 Beta steps, no Iota steps, 362,786 Zeta steps and 2,164,047 projections. It recorded 274,793 Pi-domain comparisons, 125,785 proposition comparisons and 3,342,406 proof attempts. The proposition timer (341.106 s) is nested and cannot establish an exclusive proof-type share. Pair capture covers only the first five million of 6.599 million calls, with no context identity; repeated entries consumed 1.4% of trace comparison-exclusive time. Allocation and GC attribution is unavailable. In the aligned counters root, calls drop 93%, reduction time drops 93%, and comparison time drops 93%; the small remaining root is still mixed.
