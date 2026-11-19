# NativePullTensor

Lean 4.35.0 with built Mathlib, master build revision `1ef1fddac73e`, one Lean thread, `nice -n 10`, synchronous elaboration. This is the tenth module in the handover, estimated at 410 whole-module CPU seconds from instruction counts.

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| Original, Kernel on | 272.53 | 268.39 | 4.15 | 7,926,140 | success |
| Original, Kernel skipped | 6.99 | 6.16 | 0.85 | 2,661,816 | diagnostic success |
| [HotBodiesSorry.lean](probes/HotBodiesSorry.lean) | 154.51 | 152.56 | 1.97 | 6,162,640 | diagnostic warning |

The per-declaration profiler reports four major type-check times in source order:

| Declaration | Original check | Typed-`sorry` body check |
|---|---:|---:|
| `exists_nativePullTotalTensor` | 51.5 s | 48.9 s |
| `nativePullTotalTensor` | 80.5 s | 24.1 s |
| `nativePullTotalTensor_summands` | 79.3 s | 51.1 s |
| `nativeRestrictionDerivedTensor` | 52.5 s | 23.7 s |

Cumulative original type checking is 265 s; tactics total 0.751 s. Source-prefix controls validate the order: [ThroughTotalExistence.lean](probes/ThroughTotalExistence.lean) checks the first at 51.4 s (56.92 s whole file); [ThroughTotalSummands.lean](probes/ThroughTotalSummands.lean) includes the next two at 79.9 and 80.9 s (218.74 s whole file); [ThroughModelNaturality.lean](probes/ThroughModelNaturality.lean) adds only about one second; [ThroughRestrictionDerivedTensor.lean](probes/ThroughRestrictionDerivedTensor.lean) adds the final 52.2 s (272.62 s whole file). The final `nativePullTensor` declaration adds no separately visible check above 50 ms. Replacing three earlier abstract normalization bodies with `sorry` left cumulative type checking at 265 s, so those are not the hotspot.

Command form from the master build tree (replace `SOURCE`):

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 SOURCE
```

The skipped run adds `-Ddebug.skipKernelTC=true`. All `sorry` files and skip are diagnostic only.
