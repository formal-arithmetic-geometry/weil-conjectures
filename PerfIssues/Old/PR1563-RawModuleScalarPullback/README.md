# PR #1563: raw module scalar pullback formula

Ported historical theorem body versus current fixed body over the same current source prefix, Lean 4.35.0, master build revision `1ef1fddac73e`, single Lean thread, `nice -n 10`, synchronous elaboration. Both files retain today's abstract helper, so the comparison isolates the final proof form; the historical PR's whole-module environment is not recreated.

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| [Before.lean](Before.lean) | 117.04 | 115.92 | 1.32 | 8,008,236 | success with unused-simp warnings |
| [After.lean](After.lean) | 50.98 | 50.00 | 0.99 | 5,146,444 | success |
| Before, Kernel skipped | 16.06 | 15.47 | 0.79 | 3,048,448 | diagnostic success |
| [TargetSorry.lean](probes/TargetSorry.lean) | 57.26 | 56.17 | 1.11 | 5,146,792 | diagnostic warning |

Per-declaration profiler: the shared current helper `higherDirectImageRawOverPullback_eq_moduleFactors` checks in 32.4-32.7 s in both real forms. The target `rawModuleScalar_pullback_module_formula` checks in **68.2 s** historical versus **15.2 s** fixed. With the target body replaced by `sorry`, its declaration still takes 21.6 s to check; this is a control in a changed Kernel context and shows that the type itself is not free. Cumulative type checking: 101 s before, 47.9 s after, 54.3 s with `sorry`, 0.433 ms with Kernel skipped. The historical `simp only` emits unused-argument warnings under today's imports but succeeds.

Command form from the master build tree (replace `SOURCE`):

```sh
LEAN_NUM_THREADS=1 timeout 1200 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 SOURCE
```

The skipped control adds `-Ddebug.skipKernelTC=true`. Skip and `sorry` are diagnostic only.
