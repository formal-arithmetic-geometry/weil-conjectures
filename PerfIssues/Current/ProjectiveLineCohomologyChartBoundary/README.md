# ProjectiveLineCohomologyChartBoundary

Lean 4.35.0, master build revision `1ef1fddac73e`, built Mathlib, one Lean thread, `nice -n 10`, synchronous elaboration. Handover estimate: 906 whole-module CPU-s from instruction counts. Measured whole-file profile:

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| Original, Kernel on | 372.17 | 371.31 | 0.92 | 3,213,756 | success |
| Original, Kernel skipped | 357.69 | 356.85 | 0.90 | 2,868,480 | diagnostic success |
| [ClassEqSorry.lean](probes/ClassEqSorry.lean) | 198.26 | 197.34 | 0.99 | 3,216,244 | diagnostic warning |
| [FinalRefineSorry.lean](probes/FinalRefineSorry.lean) | 192.36 | 191.46 | 0.96 | 3,195,636 | diagnostic warning |
| [FirstRefineSorry.lean](probes/FirstRefineSorry.lean) | 194.95 | 194.08 | 0.93 | 3,197,976 | diagnostic warning |
| [BothSorry.lean](probes/BothSorry.lean) | 17.96 | 17.10 | 0.93 | 3,193,124 | diagnostic warning |

Profiler top list in source order: `chartBoundaryClass_eq` has `Lean.Parser.Tactic.exact` at 172 s; `exists_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass` has `Lean.Parser.Tactic.refine` at 174 s and the following `exact` at 1.94 s. Type checking of these declarations is 3.43 and 3.52 s. Earlier checks include 3.39 and 3.44 s. Cumulative tactic execution: 350 s; cumulative type checking: 14.5 s. Profiler output omits declaration names; unique source calls and the one-line probes confirm the mapping.

Command form from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 \
  WeilConjectures/EtaleCohomology/Purity/Smooth/ProjectiveLineCohomologyChartBoundary.lean
```

The skipped run adds `-Ddebug.skipKernelTC=true` and still spends 172 s in `exact` and 174 s in `refine`; cumulative type checking falls to 5.09 ms. All `sorry` variants and Kernel skipping are diagnostic only.
