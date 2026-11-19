# `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralBoundaryRefinementNormalization`

Radar estimate (whole module, `6f9ee9b2fd1`): ≈ 378 s CPU. Measured here: **173 s CPU, 185 s wall without `trace.profiler`.** The prescribed command with `trace.profiler` takes 660 s CPU. The extra ≈ 490 s is spent pretty-printing the 35,000-line trace, whose nodes contain huge terms; it is not compilation cost. Almost all of the real cost (162 s) is one theorem, `integral_boundaryRefinement_normalization`.

## Setup

- **Commit:** `master` at `35ad26a6a7f` (2026-11-19). Radar's estimates refer to `6f9ee9b2fd1`; this file is byte-identical in `6f9ee9b2fd1`, `c63c75a53b7` and master.
- **Toolchain:** `leanprover/lean4:v4.35.0`, Mathlib `56a005855ea1`.
- **Machine (pod):** cgroup limit of 8 CPUs (`cpu.max` 800000/100000) on a 24-thread AMD Ryzen 9 7900 host, plus a 16 GiB memory limit (host: 61 GiB). The host is shared: load average 75–110 and IO pressure 60–80 % during the runs. Wall-clock and profiler times are therefore inflated compared with an idle machine. User CPU time is the most stable number.
- **Imports:** master's own build was not available in the pod. The fuxi cache endpoint is unreachable from the sandbox, and the newest master build in the pod's `/lake-cache` is `c63c75a53b7`, 48 commits behind. Rebuilding the ~9,000 changed dependencies was not feasible. So the file was compiled against the c63c75a build:
  - c63c75a's revision archives were unpacked into `.lake/build`.
  - 1,771 modules whose c63c75a archives had been evicted were filled in from the `38db2c4` build. Those modules differ between the two commits only in docstrings and comments (#2656).
  - `Weil.Definitions` was built locally.

  Dependencies therefore have the state of c63c75a, not master (the commits in between include the heartbeat clean-ups #2657 and #2667 and docstring-only chunks). The target file itself is master's version.
- **Command** (the prompt's command with the lakefile `leanOptions` passed explicitly, plus `-o` so that `.olean` export is included as in `lake build`):
  `LEAN_NUM_THREADS=3 rtime lake env lean -Dbackward.isDefEq.respectTransparency=false -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -Dweak.linter.style.header=false -Dwarn.sorry=false -Dpp.unicode.fun=true -Dprofiler=true -Dprofiler.threshold=2000 -Dtrace.profiler=true -Dtrace.profiler.threshold=2000 -o /tmp/x.olean File.lean`.
  `/usr/bin/time` is missing in the pod, and the cgroup's `memory.peak` is cumulative and read-only. `rtime` is a small Perl substitute: wall time, children's user/sys CPU, and peak RSS sampled from `VmHWM` every 0.2 s.
- **Elaboration vs kernel:** a second run of the same command with `-Ddebug.skipKernelTC=true`. Per-declaration kernel times come from the `[Kernel] typechecking declarations` trace nodes of the primary run. "< 2" means no kernel node reached the 2 s trace threshold.

## Module-level numbers

| run | wall s | user CPU s | sys s | peak RSS |
|---|---|---|---|---|
| primary (profiler + `trace.profiler`, `-o`) — prescribed command | 688.8 | 660.2 | 2.5 | 3.32 GB |
| profiler only, `-o` (no `trace.profiler`) | 184.9 | 173.1 | 2.4 | 3.30 GB |
| profiler only, no `-o` | 180.9 | 172.5 | 1.7 | 3.31 GB |
| `-Ddebug.skipKernelTC=true` (+ trace, `-o`) | 670.8 | 647.4 | 2.5 | 3.30 GB |

Comparing the rows: `.olean` export is negligible (< 1 s), the kernel costs ≈ 6 s, and `trace.profiler` output adds ≈ 490 s. None of the profiler categories contain that trace cost.

Time split (cumulative profile of the run without `trace.profiler`, profiler seconds):

| category | s |
|---|---|
| elaboration: tactic execution | 163 |
| elaboration: elaboration (terms) 2.9, `do` elaborator 2.3, typeclass inference 2.5, interpretation 1.3, simp 0.3 | 9.3 |
| type checking (kernel) | 6.0 |
| compilation (LCNF + IR) | 0.2 |
| `.olean` serialization | 0.2 |
| other: import 3.3, process pre-definitions 0.1, linting 0.06, parsing 0.05 | ≈ 3.5 |

## Slow declarations (≥ 30 s)

| declaration | total s | elaboration s | kernel s | classification | note |
|---|---|---|---|---|---|
| `AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.integral_boundaryRefinement_normalization` | 163 | 161.5 (same in the skipKernelTC run: tactics 32.4 + 114 + 12.4) | < 2 | elaborator defeq check (unfolding the `DerivedCategory` category instance down to `equivShrink`) | Three tactics take nearly all the time:<br>• `exact normalized_transport …` (114 s). The worst part is a 77 s `isDefEq` while `localizingRefinementMap_normalized Λ r'` propagates its expected type. Its sides are compositions of `derivedOpenImmersionLowerShriekUpperStarAdjunction` maps, and it unfolds `instCategoryDerivedCategory` → `equivShrink` → `EquivLike.coe`. Another 15 s `isDefEq` is on `(leftDerivedUpperStarIsoMapDerivedCategory Λ d.obj.i).inv.app`.<br>• The `refine` with `isIso_of_comparison_comp` (32 s). Of this, 12.8 s is unifying `hc` against `localizingRefinementMap Λ (a ≫ r') …`, through the same `equivShrink` unfolding.<br>• A final `exact` (12.5 s). |

Other declarations ≥ 2 s (none ≥ 30 s): the private `total_restriction` takes 3.2 s (custom `run_tac` instance conversion).

Raw output: `….IntegralBoundaryRefinementNormalization.profile.txt` contains:
- the primary run, trimmed to trace nodes ≥ 1 s with each node cut to its first 300 characters;
- the two runs without trace;
- the skipKernelTC run.
