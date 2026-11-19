# CompletedScalarOrdinaryCoherence

Lean 4.35.0 with built Mathlib, master build revision `1ef1fddac73e`, single-threaded synchronous elaboration. Handover estimate: 691 CPU-s by module instruction count. Measured complete source:

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| Original, Kernel on | 305.65 | 304.79 | 0.88 | 2,729,280 | success |
| Original, Kernel skipped | 303.85 | 303.02 | 0.85 | 2,700,052 | diagnostic success |
| [CounitNaturalitySorry.lean](probes/CounitNaturalitySorry.lean), Kernel on | 12.15 | 11.37 | 0.82 | 2,677,884 | diagnostic warning |

Per-declaration profiler: `counit_naturality` (source lines 237-248) has one `Lean.Parser.Tactic.exact` call at 293 s; its proof term type checks in 0.423 s. Later declarations show no tactic over 1 s. Cumulative tactic execution: 296 s original; cumulative Kernel type checking: 2.01 s. The `sorry` probe retains the module after the target and takes about 12 s, with 2.02 s cumulative type checking. Profiler output omits declaration names; source order and the unique long `exact` identify the call.

Command form from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 \
  WeilConjectures/SmoothPurity/CompletedLineTensor/CompletedScalarOrdinaryCoherence.lean
```

The skipped control adds `-Ddebug.skipKernelTC=true`; its long `exact` is still 293 s. Kernel skipping and the `sorry` probe are diagnostic controls only.
