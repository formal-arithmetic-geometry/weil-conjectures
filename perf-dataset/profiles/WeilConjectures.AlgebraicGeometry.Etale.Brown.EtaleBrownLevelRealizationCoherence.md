# `WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelRealizationCoherence`

Radar estimate (whole module, `6f9ee9b2fd1`): ≈ 349 s CPU. Measured here (master's version of the file): **246 s CPU, 263 s wall.** Of this, 253 s is kernel type checking and about 8 s is everything else. The kernel spends 194 s on the three auxiliary proofs of the private `ordinaryRestrictionIso` and 49 s on `etaleBrownLevelRealizationCoherence_exists`. In the trace the five kernel checks ran one after another (wall ≈ their sum), not in parallel on the 3 threads.

## Setup

- **Commit:** `master` at `35ad26a6a7f` (2026-11-19). Radar's estimates refer to `6f9ee9b2fd1`; this file is identical in `6f9ee9b2fd1` and master, but it changed between `c63c75a53b7` and master (heartbeat clean-up PR #2657). Master's version was compiled against the c63c75a build; its direct imports are identical and unchanged in both commits. The c63c75a version was also profiled, for comparison (see below).
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
| primary (profiler + trace, `-o`), master's file | 262.9 | 246.2 | 5.9 | 6.08 GB |
| `-Ddebug.skipKernelTC=true`, master's file | 12.1 | 7.9 | 2.0 | 3.68 GB |
| superseded first run (an orphaned compile of another module ran at the same time) | 384.8 | 253.7 | 11.4 | 5.61 GB |
| c63c75a's version of the file, same command | 318.0 | 288.1 | 12.8 | 7.19 GB |

Time split from the cumulative profile of the primary run (profiler seconds):

| category | s |
|---|---|
| type checking (kernel) | 256 |
| elaboration: tactic execution 5.7, typeclass inference 1.3, elaboration 0.9, interpretation 0.7 | 8.6 |
| compilation | 0 (not listed) |
| `.olean` serialization | 0.1 |
| other: import 3.7, process pre-definitions 0.2, linting 0.1 | ≈ 4.1 |
| ("blocked (unaccounted)" 253 s is the module linter waiting for the kernel tasks; it is not extra CPU) | |

## Slow declarations (≥ 30 s)

| declaration | total s | elaboration s | kernel s | classification | note |
|---|---|---|---|---|---|
| `AlgebraicGeometry.ordinaryRestrictionIso` (private def, `maxHeartbeats 2000000`) | 195 | < 2 | 194.4 | kernel unfolding / defeq check | The cost is the three proofs abstracted from `NatIso.ofComponents (… ObjectProperty.isoMk (NatIso.ofComponents (… ModuleCat.isoMk (Iso.refl _) …)))`; the rows below give the breakdown. The `?_` ↔ `_proof_k` mapping was checked with `#check` in a scratch copy. |
| ↳ `ordinaryRestrictionIso._proof_3` | 114 | – | 113.8 | kernel defeq check | Naturality in the module `M` (`intro M N f; ext U x; rfl`). The kernel unfolds both constant-scalar restriction constructions to check the `rfl`. |
| ↳ `ordinaryRestrictionIso._proof_2` | 48 | – | 47.8 | kernel defeq check | Naturality in the étale open `U` (`intro U V f; ext x; rfl`). |
| ↳ `ordinaryRestrictionIso._proof_1` | 33 | – | 32.7 | kernel defeq check | Scalar linearity of `Iso.refl` (`ext x; change …; exact congrArg … (toSheafify_naturality …)`). The `change` makes the kernel check the expanded sheafified-section expressions. |
| `AlgebraicGeometry.etaleBrownLevelRealizationCoherence_exists` | 52 | 3.3 | 48.8 | kernel defeq check | Scratch probes, checking the kernel on this theorem only:<br>• Replacing the bullets `brownCoherenceGenericSections … rfl`, `exact hrestriction` and `exact hscalar` with `sorry`, together or one at a time, removes only 0–7 s.<br>• `sorry` right after the two `choose` steps leaves only 5 s.<br>So ≈ 36 s is the kernel checking the assembled structure `R' := { …, ordinaryRestriction := ordinaryRestrictionIso O t W, restriction := restriction, scalar := scalar }` in `refine ⟨⟨R', ?_⟩⟩` against `StrictEtaleBrownRealizationCoherence … R'`. In c63c75a's version this theorem took 114 s in the kernel; master's restructuring (#2657) brought it to 49 s. |

Other declarations ≥ 2 s (none ≥ 30 s): the private `brownCoherenceDerivedRestriction` takes 11.8 s (elaboration 2.3 s, kernel 9.5 s).

Kernel times in the c63c75a version of the file, for comparison: `ordinaryRestrictionIso._proof_2/_3/_4` 31.3 / 49.0 / 116.3 s (the numbering is shifted by one), `etaleBrownLevelRealizationCoherence_exists` 114.0 s.

Raw output: `….EtaleBrownLevelRealizationCoherence.profile.txt` contains:
- the primary run, complete;
- trimmed copies of the superseded run, the skipKernelTC run, the `#check` probe (`Brown_probe1`), the seven kernel probes (`Brown_probe2a`–`g`: a = only the main theorem kernel-checked, b–g = the `sorry` variants above), and the c63c75a run.
