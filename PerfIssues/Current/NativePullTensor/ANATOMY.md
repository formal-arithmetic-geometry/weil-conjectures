# DefEq Cost Anatomy Report

Case: NativePullTensor
Lean / Mathlib: Lean 4.35.0, source snapshot 1ef1fddac73
Kernel instrumentation: observational Lean 4.35.0 patch, counters and detailed-trace modes from READY-4.35.0; minimum reported root 100 ms.

Root: NPT-final inferred/declared type conversion. In-situ module: 295.88 s wall, 294.27 s user CPU, 8,005,044 KB RSS. ValuePrefixes measured dependent Exists.choose domains at 22,998 ms and 23,068 ms. MajorAlignment measured endpoint conversions at 11,450 ms and 11,489 ms; aligned pairs were 0 ms and reverse restoration 11,363 ms.

Counters-only roots 591 and 604 took 34.078/34.768 s, with 2,685,580/2,685,543 recursive calls and maximum depths 81/74. Mutually exclusive time was 22.333/22.504 s comparison (65.5/64.7%) and 11.746/12.264 s reduction (34.5/35.3%). Root 591 had 3,246,736 WHNF calls, 1,905,300 Delta unfolds, 2,387,860 Beta steps, 47,872 Iota steps, and 136,478 projections. Delta accounted for only 330 ms; Functor.obj unfolded 516,742 times in 118 ms, so high unfold count was not itself the main expense.

The detailed trace reproduced 2,685,580 calls and depth 81. Fan-out included 2,137,132 leaves and nodes with up to 28 children. The raw pair capture counted 842,601 exact pairs, 1,842,979 repeated entries, and 638,120 structural groups; repeated entries contributed 2.230 s of exclusive comparison time (8.8% of the trace root's exclusive comparison time). The exact-pair key did not record local context, and the repeated-pair timer excludes reduction, so this is a bounded repetition observation.

Top exclusive children included Functor.map (114.5 ms), tensor_map_comm (112.9 ms), map_unit_comp_str (55.7 ms), Functor.modObjObj (54.1 ms), and Functor.flip._proof_4 (52.7 ms). The complete top-20 list and depth/fan-out histograms are in the trace artifact.

Proposition comparisons numbered 32,060, but the proposition timer is nested and cannot be added to root exclusive categories. Allocation/GC counters were unavailable; trace peak RSS was 8,175,456 KB. The measured workload is mixed (outcome F), comparison-leaning, deep, and moderately wide. Alignment removes the measured conversion; exact dependent/proof-type exclusive shares remain unresolved.

## Reproducibility and cost accounting

Root ID 591 is a reported Kernel conversion during `HeadAudit.lean`'s check of `nativePullTotalTensor`. That probe obtains the inferred and declared type `Expr`s with `Kernel.check` and `getConstInfo`, but the instrumentation does not print their full expressions for this root. The two release `Exists.choose` domain checks in `ValuePrefixes.lean` are distinct sites; their pair identity across sites was not recorded. The original source and the release alignment/reversal control are in `probes/anatomy/original/` and `MajorAlignment.lean`. Counters and trace output, including every reported branch, depth and fan-out bucket and the ranked 20 child calls (parent ID, depth, heads, exclusive/inclusive times), are in `probes/anatomy/HeadAudit.root-counters.metrics.txt` and `HeadAudit.trace.metrics.txt`. The alignment counters are in `MajorAlignment.control-counters.metrics.txt`.

For root 591, trace mode recorded 537,023 proof-irrelevance attempts, 32,060 proposition comparisons, 189,446 application attempts and 21 Pi-domain comparisons. The proposition timer (131.534 s) is inclusive and overlaps recursive calls; it does not establish a 131 s proof-type contribution. WHNF took 12.134 s in trace mode; Delta took 343 ms within it. Beta/Iota/projection counts have no separate exclusive timers. The comparison timer (25.373 s) also includes dependent and proof-type work, so those subcategories cannot be added as independent shares. Expr allocations, allocated bytes, live heap and GC time were not exposed; RSS is only a process proxy. The aligned pair is below the 100 ms reporting threshold; restoring the endpoint brings back an 11.363 s release conversion. The remaining parent cost beyond the isolated accessor checks cannot be partitioned without a parent-to-child trace linking those separate checks.
