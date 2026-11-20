# DefEq Cost Anatomy Report

Case: PR1563-RawModuleScalarPullback
Lean / Mathlib: Lean 4.35.0, source snapshot 1ef1fddac73
Kernel instrumentation: observational Lean 4.35.0 patch, counters and detailed-trace modes from READY-4.35.0; minimum reported root 100 ms.

Root: seven-argument CategoryStruct.comp. Original target spans 33.3 s and 114 s; CPU 150.24 s; wall 164.38 s; RSS 10,059,884 KB. Correct replay arguments were 1, 0, 2,331, 2,274, 2,387, 6,809, and 22,374 ms. Aligned source: 52.07 s wall, 4,798,288 KB RSS. Several children materially contribute, led by nested CategoryStruct.comp at 22.374 s and Functor.map at 6.809 s.

The largest counters-only replay root took 33.224 s with 2,573,989 recursive calls, depth 95, 16.070 s exclusive comparison (48.4%) and 17.154 s reduction (51.6%). A second 30.540 s root had 2,551,055 calls, depth 89, and nearly even 15.186/15.354 s shares. These are separate replays, not additive child timings. Counters peak RSS was 21,535,948 KB versus 10,059,884 KB release. Proposition timers overlap nested work; allocation/GC counters were unavailable.

This is a distributed, mixed (outcome F) composition workload.

Detailed root 7709 took 40.875 s with 2,573,989 calls and depth 95. Its bounded full pair capture found 1,723,710 distinct exact pairs, 850,279 repeated entries, and 1,340,930 structural groups. Repeated entries contributed 409 ms exclusive comparison time; local-context identity was not recorded. Top exclusive children included HSMul.hSMul (1.111 s), NSMul.proj (235 ms), Add.add (108 ms), and SemigroupAction.proj (52 ms). The seven argument replays and the trace together show several costly subproblems, not one leaf.

The aligned module still had a 20.699 s / 1,728,196-call counters root, comparable to a 20.047 s / 1,728,196-call root in the original replay. The higher 33.224/30.540 s roots disappear, but substantial shared module work remains. Trace peak RSS was 22,085,548 KB; this is an instrumented-process proxy, not allocated bytes.

## Reproducibility and cost accounting

Root ID 7709 is the largest replayed `CategoryStruct.comp` conversion. The exact seven arguments in the full dependent application are preserved by `probes/anatomy/replay/WeilConjectures/AlgebraicGeometry/RawModuleScalarPullbackModuleFormula.lean`; the original and aligned modules are in sibling directories. The seven release argument timings identify several expensive arguments, including the seventh at 22.374 s, but their sum is not an exclusive parent decomposition. The replay `*.root-counters.metrics.txt` and `*.trace.metrics.txt` and aligned `*.aligned-counters.metrics.txt` contain the complete root summaries, ranked 20 child calls and depth/fan-out distributions; maximum fan-out across trace roots is 25.

Trace root 7709 made 8,470,713 WHNF requests (18.647 s), 4,993,230 Delta unfolds (580 ms), 4,920,191 Beta steps, no Iota steps, 139,056 Zeta steps and 833,125 projections. It recorded 116,765 Pi-domain comparisons, 48,776 proposition comparisons and 1,296,043 proof attempts. The 120.785 s proposition timer overlaps descendants, so neither it nor the release argument timings can be added to the 22.228 s trace comparison-exclusive time. The aggregate pair counts do not identify exact overlap between seven independent argument replays; local context was omitted. Repeated entries used 1.8% of trace comparison-exclusive time. No allocation or GC counters were available. The aligned module removes the two largest replay roots while retaining another comparable 20 s root, hence the control reduces some comparisons and leaves substantial shared work.
