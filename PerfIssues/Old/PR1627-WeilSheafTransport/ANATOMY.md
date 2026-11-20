# DefEq Cost Anatomy Report

Case: PR1627-WeilSheafTransport
Lean / Mathlib: Lean 4.35.0, source snapshot 1ef1fddac73
Kernel instrumentation: observational Lean 4.35.0 patch, counters and detailed-trace modes from READY-4.35.0; minimum reported root 100 ms.

Root: generated powFunctor law fields. Original field checks were 41.0 s, 55.6 s, and 14.4 s; CPU 109.65 s; RSS 7,792,432 KB. Correct replay measured dependent id proof-argument domains at 7,608 ms and 32,992 ms. Aligned source: 10.63 s wall, 1,841,708 KB RSS. Own checks were 7.734 s and 13.756 s.

The largest counters-only replay root took 40.808 s with 10,904,899 recursive calls, depth 61, 20.611 s exclusive comparison (50.5%) and 20.198 s reduction (49.5%). Other generated-field roots had distinct sizes, including 19.088 s / 4,696,766 calls and 17.225 s / 4,696,766 calls. Their nested proposition timers cannot be added to exclusive root time. Counters mode did not capture pair identities or allocations; its peak RSS was 16,197,888 KB versus 7,792,432 KB release.

The detailed trace's largest root took 47.557 s with the same 10,904,899 calls and depth 61. It split into 25.678 s exclusive comparison and 21.879 s reduction. In the bounded first 5,000,000 calls, 1,844,240 exact pairs were distinct, 3,155,760 were repeats, and repeated entries contributed 2.865 s exclusive comparison time. It captured 3,726 proposition pairs, of which 2,486 were distinct and 1,240 repeated. Local-context identity was not recorded, so these are raw expression-pair statistics. Trace peak RSS was 17,434,456 KB. The aligned source counters emitted no root above 100 ms, indicating that its generated comparisons disappeared.

The profile is mixed (outcome F), dependent generated-field work with similar id/application shape but distinct root costs. Repetition is present in the bounded trace but does not dominate measured exclusive comparison time. The top-20 child list and fan-out histogram are preserved in the trace artifact.

## Reproducibility and cost accounting

The generated `powFunctor` field checks run in the original module under `probes/anatomy/original/`; the release `id` domain replay and aligned source are under `replay/` and `aligned/`. The exact dependent field expressions are preserved there, although the instrumented root lines do not print full left/right expressions. Root ID 1539 is the largest replayed conversion. The replay `*.root-counters.metrics.txt` and `*.trace.metrics.txt` preserve each root, the ranked 20 child calls and depth/fan-out histograms; maximum fan-out across trace roots is 18. The aligned `*.aligned-counters.metrics.txt` is empty because no conversion crossed 100 ms.

Trace root 1539 made 7,231,443 WHNF requests (21.879 s), 2,539,771 Delta unfolds (278 ms), 4,193,774 Beta steps, no Iota or Zeta steps, and 110,104 projections. It entered 3,726 proposition comparisons and 3,500,726 proof attempts, but no Pi-domain comparison; the costly release domain is a proposition argument in an application, not a reported Pi-domain event in this trace. The proposition timer was 8.056 s and is nested. Proposition pair groups and their top heads are in the trace artifact, but per-field exact-pair overlap is not recorded across independent roots. The 5,000,000-call pair sample excludes later calls and local context. Repeated entries used 11.2% of this root's trace comparison-exclusive time. No Expr allocation, allocated-byte, live-heap or GC measurement was available, and the process RSS increase cannot establish an allocation bottleneck. The aligned source removes every reported >100 ms conversion at this site; it changes the construction, so a per-call speed comparison is unavailable.
