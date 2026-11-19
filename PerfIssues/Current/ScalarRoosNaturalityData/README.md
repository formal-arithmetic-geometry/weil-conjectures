# ScalarRoosNaturalityData

Master build revision `1ef1fddac73e`, Lean 4.35.0 and its built Mathlib, one Lean thread, `nice -n 10`, synchronous elaboration. The historical handover estimated about 694 CPU seconds for the whole module from instruction counts; the measured full-file run is 305.94 user-facing wall seconds and 305.03 user CPU seconds.

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| Original, Kernel on | 305.94 | 305.03 | 0.93 | 2,826,620 | success |
| Original, Kernel skipped | 301.44 | 300.60 | 0.86 | 2,754,752 | diagnostic success |
| [NaturalitySorry.lean](probes/NaturalitySorry.lean), Kernel on | 13.17 | 12.34 | 0.85 | 2,830,572 | diagnostic warning |

Per-declaration profiler highlights, in source order:

| Declaration/component | Kernel on | Kernel skipped |
|---|---:|---:|
| `fraction_naturality`, type checking | 0.520 s | skipped |
| `scalarRoosBridgeNat`, type checking | 1.81 s | skipped |
| `completedCounitNat.naturality`, `Lean.Parser.Tactic.exact` | **292 s** | **297 s** |
| `completedCounitNat`, type checking | 0.411 s | skipped |
| `scalarLimitComparison`, type checking | 5.81 s | skipped |
| Cumulative tactic execution | 293 s | 297 s |
| Cumulative type checking | 8.61 s | 0.00215 s |

The per-declaration mapping uses source order and the unique long `exact` in the file; the profiler log itself omits declaration names. The exact line is in `completedCounitNat.naturality`.

Command form from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 \
  WeilConjectures/TraceFormula/Scalar/ScalarRoosNaturalityData.lean
```

The skipped run adds `-Ddebug.skipKernelTC=true`; the local probe uses the same command with its own source path. Skipping Kernel checking and `sorry` are diagnostic controls only.
