# ScalarModelRoosZeroLiftFactorizationFromCoordinates

Lean 4.35.0 with built Mathlib, master build revision `1ef1fddac73e`, one Lean thread, `nice -n 10`, synchronous elaboration. The handover estimated 687 whole-module CPU seconds by instruction count. The unchanged whole source is **not a valid completed baseline**: it exits 1 after 303.18 s wall, 302.30 s user CPU, 0.91 s system CPU, and 2,783,076 KB peak RSS, with `simp made no progress` at line 182 (a type mismatch involving a cast between two coefficient-restriction objects). Its first private theorem succeeds before that error.

The probes end immediately after `scalarCounit_natural`, the valid first theorem, and close the namespace:

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| [CounitPrefix.lean](probes/CounitPrefix.lean), Kernel on | 295.17 | 294.31 | 0.87 | 2,784,552 | success |
| Same prefix, Kernel skipped | 296.07 | 295.22 | 0.86 | 2,755,624 | diagnostic success |
| [CounitSorry.lean](probes/CounitSorry.lean), Kernel on | 2.92 | 2.12 | 0.82 | 2,723,976 | diagnostic warning |

The per-declaration profiler assigns 292 s to the sole `Lean.Parser.Tactic.exact` in `scalarCounit_natural`, while checking its proof term takes 0.404 s. The full failing run shows the same 292 s `exact` and 0.404 s type check before its later error. Replacing that block with `sorry` cuts the valid prefix to 2.92 s.

Command form from the master build tree (replace `SOURCE`):

```sh
LEAN_NUM_THREADS=1 timeout 900 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 SOURCE
```

The skipped control adds `-Ddebug.skipKernelTC=true`. Neither the failed whole module nor a diagnostic control is counted as a successful whole-module compile.
