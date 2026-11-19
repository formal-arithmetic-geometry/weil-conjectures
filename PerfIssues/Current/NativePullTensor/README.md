# NativePullTensor

Lean 4.35.0 with built Mathlib, master revision `1ef1fddac73e`, one thread, synchronous elaboration, `nice -n 10`. The source is the tenth module in the handover, estimated at 410 whole-module CPU seconds from instruction counts.

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| Original, Kernel on | 272.53 | 268.39 | 4.15 | 7,926,140 | success |
| Original, Kernel skipped | 6.99 | 6.16 | 0.85 | 2,661,816 | diagnostic success |
| [HotBodiesSorry.lean](probes/HotBodiesSorry.lean) | 154.51 | 152.56 | 1.97 | 6,162,640 | diagnostic warning |
| [AllTypesOnly.lean](probes/AllTypesOnly.lean) | 55.22 | 54.29 | 0.95 | 4,414,996 | diagnostic axioms |
| [NativeDiagnostics.lean](probes/NativeDiagnostics.lean) | 272.88 | 271.43 | 4.09 | 7,942,652 | diagnostic success |

The original per-declaration Kernel checks, in source order, are `exists_nativePullTotalTensor` 51.5 s, `nativePullTotalTensor` 80.5 s, `nativePullTotalTensor_summands` 79.3 s, and `nativeRestrictionDerivedTensor` 52.5 s. The final `nativePullTensor` is cheap. Source-prefix controls in `probes/` reproduce their order and the typed-placeholder control shows a substantial type/context floor. The [classification](CLASSIFICATION.md) records the direct Kernel type/value replay, `Exists.choose` argument-prefix bisection, expression-pair diff, self-versus-cross control, and unfold counts.

Command form from the master build tree, replacing `SOURCE` with the scratch probe path:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 SOURCE
```

The skipped run adds `-Ddebug.skipKernelTC=true`. All `sorry` and axiom sources are diagnostic only.
