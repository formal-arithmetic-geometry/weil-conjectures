# `WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarOrdinaryCoherence`

Radar estimate (whole module, `6f9ee9b2fd1`): ≈ 691 s CPU. Measured here: **363 s CPU, 376 s wall.** Almost all of it (331 s) is the `exact` in one private lemma, `counit_naturality`.

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
| primary (profiler + trace, `-o`) | 375.8 | 362.7 | 2.5 | 3.25 GB |
| `-Ddebug.skipKernelTC=true` | 371.7 | 360.0 | 2.4 | 3.19 GB |

Time split from the cumulative profile of the primary run (profiler seconds):

| category | s |
|---|---|
| elaboration: tactic execution | 338 |
| elaboration: interpretation (meta code) | 16.2 |
| elaboration: elaboration (terms) | 6.4 |
| elaboration: typeclass inference | 3.3 |
| type checking (kernel) | 4.1 |
| compilation (LCNF + IR) | 0.01 |
| `.olean` serialization | 0.18 |
| other: import 3.8, process pre-definitions 0.4, linting 0.15, share common exprs 0.15, simp/dsimp 0.15 | ≈ 4.7 |

## Slow declarations (≥ 30 s)

| declaration | total s | elaboration s | kernel s | classification | note |
|---|---|---|---|---|---|
| `WeilConjectures.CompletedLineTensor.counit_naturality` (private) | 332 | 331 (334 in the skipKernelTC run) | < 2 | elaborator defeq check (`with_unfolding_all exact`) | `with_unfolding_all exact homotopyCounit_naturality … (completedScalarChangeData …).choose_spec…choose` takes 331 s. One `isDefEq` against the goal costs 318 s. It unfolds `DerivedCategory` composition (`MorphismProperty.instCategoryLocalization._aux_5`) and then compares two `Exists.choose` terms through their propositions (`IsLeftDerivedFunctor`, `IsIso ε.app …`); the two branches cost 209 s and 109 s. |

Other declarations ≥ 2 s (none ≥ 30 s): `completedScalarTensorSection_smul` 4.5 s, `derived_pentagon_aux` 2.6 s, `changeOfRings_tensor_smul` 2.2 s. All are elaboration.

Raw output: `WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarOrdinaryCoherence.profile.txt`, which has the primary run and the skipKernelTC run, trimmed to trace nodes ≥ 1 s.
