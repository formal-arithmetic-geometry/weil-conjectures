# CompletedLineOrdinaryEvaluation

Lean 4.35.0, master build revision `1ef1fddac73e`, built Mathlib, `LEAN_NUM_THREADS=1`, `nice -n 10`, and `-DElab.async=false`. The handover's 720 CPU-s was a whole-module estimate from instruction counts; the measured full-file profile is below.

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| Original, Kernel on | 326.49 | 325.80 | 1.00 | 3,043,108 | success |
| Original, Kernel skipped | 314.44 | 313.88 | 0.91 | 2,688,696 | diagnostic success |
| [CounitNaturalitySorry.lean](probes/CounitNaturalitySorry.lean), Kernel on | 30.28 | 29.68 | 0.93 | 3,048,852 | diagnostic warning |

The per-declaration profiler, read in source order, reports the largest `exact` tactic at 296 s in `counit_naturality` (lines 329-344). The next largest individual tactic is 2.25 s. Cumulative tactic execution is 307 s; cumulative Kernel type checking is 13.7 s. Notable later type checks include `pair_counit` at 3.6 s and `ordinary_evaluation_compatibility` at 3.26 s. The `sorry` control cuts cumulative tactics to 10.9 s while keeping cumulative type checking at 13.7 s. Profiler lines omit declaration names, so the mapping uses source order and the unique long call.

Command form from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 \
  WeilConjectures/SmoothPurity/CompletedLineTensor/CompletedLineOrdinaryEvaluation.lean
```

The skipped control adds `-Ddebug.skipKernelTC=true`; it still spends 298 s in the same `exact`. The `sorry` copy is diagnostic only. A Round 3 profiler-filtered trace isolates a 287.140 s `Meta.isDefEq` call with two approximately 89 s comparisons of chosen counit components; see [CLASSIFICATION.md](CLASSIFICATION.md).
