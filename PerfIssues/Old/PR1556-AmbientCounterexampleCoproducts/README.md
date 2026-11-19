# PR #1556: ambient counterexample coproducts

Lean 4.35.0, master build revision `1ef1fddac73e`, single thread, `nice -n 10`, synchronous elaboration. Both files use the current source prefix and end after `not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`. The sole proof difference is the historical closing `simpa` versus the merged `cancel_mono` step.

| Source | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| [Before.lean](Before.lean) | 60.57 | 59.47 | 1.11 | 7,760,464 | success |
| [After.lean](After.lean) | 5.73 | 4.75 | 0.93 | 3,056,716 | success |
| Before, Kernel skipped | 3.55 | 2.68 | 0.89 | 3,056,716 | diagnostic success |
| [ClosingSorry.lean](probes/ClosingSorry.lean) | 5.66 | 4.76 | 0.92 | 3,058,444 | diagnostic warning |

Per-declaration profiler: historical target type checking 54.9 s; preceding theorem type checking 2.03 s. Fixed target has no >=50 ms type-check line; preceding theorem 2.02 s. Cumulative type checking is 57.0 s before and 2.05 s after. The historical `simpa` tactic itself is below the 50 ms profiler threshold; the cost arrives when its proof term is Kernel checked.

Command form, from the master build tree (replace `SOURCE`):

```sh
LEAN_NUM_THREADS=1 timeout 900 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 SOURCE
```

The skipped control adds `-Ddebug.skipKernelTC=true`. The `sorry` probe is diagnostic only.
