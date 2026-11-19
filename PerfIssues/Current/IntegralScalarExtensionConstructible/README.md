# IntegralScalarExtensionConstructible

Master build revision `1ef1fddac73e`, Lean 4.35.0, one Lean thread, `nice -n 10`, synchronous elaboration, and profiler threshold 50 ms. The source is the current module `WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible`.

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| Original, Kernel on | 226.40 | 225.58 | 1.03 | 2,788,524 | success |
| Original, Kernel skipped | 211.26 | 210.62 | 0.84 | 2,646,892 | diagnostic success |
| Early `integralScalarExtension_constructible` body `sorry` | 229.38 | 228.61 | 0.98 | 2,788,696 | diagnostic success |
| Full-file `completedScalarChainComparison_isIso` with only `h2` witness `sorry` | 29.06 | 28.39 | 0.88 | 2,743,316 | diagnostic success |

The original profiler has one 196 s `Lean.Parser.Tactic.refine`; cumulative Kernel type checking is about 15.3 s. Kernel skipping preserves the long refine, while replacing the early constructibility theorem does not. The full-file witness control removes it.

Selected staged probes in `probes/` compile valid source prefixes or diagnostic copies. `BeforeCompletedComparisonIso` stops before the expensive declaration (11.81 s wall). `BeforeOrdinaryCompletedIso` includes the declaration and takes 210.61 s wall, with a 197 s `refine`. `ChainAfterH1` retains the preceding `h` and `h1` and takes 13.25 s; `ChainAfterH2` adds the real `h2` witness and takes 208.99 s; `ChainH2WitnessSorry` replaces only that witness with `sorry` and takes 13.12 s. `H2WitnessSorryFull` confirms the same control in the full source (29.06 s wall). `ChainAfterH3` shows the following composition and rewrite do not add the hotspot.

All `sorry` and Kernel-skip runs are diagnostic controls, not proof results. Commands used a per-process timeout no greater than 900 seconds and were run from the existing master build tree; no build artifacts were written to the report worktree.
