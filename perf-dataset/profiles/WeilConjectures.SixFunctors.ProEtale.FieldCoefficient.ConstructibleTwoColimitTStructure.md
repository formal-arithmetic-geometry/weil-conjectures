# `WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstructibleTwoColimitTStructure`

Radar estimate (whole module, `6f9ee9b2fd1`): ≈ 317 s CPU. Measured here: **152 s CPU, 130 s wall.** The four slow declarations all hit the same elaborator defeq problem. The `t`-structure `constructibleTwoColimitTStructure` is built with `StageSystem.tStructure` and unfolded against the named halves `constructibleTwoColimitLE`/`GE` and `constructibleTwoColimitHeart`. Each such check costs 10–27 s and is repeated 2–3 times per declaration.

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
| primary (profiler + trace, `-o`) | 130.0 | 152.0 | 2.7 | 3.57 GB |
| `-Ddebug.skipKernelTC=true` | 122.5 | 148.6 | 2.9 | 3.54 GB |

Time split from the cumulative profile of the primary run (profiler seconds; the proofs are elaborated asynchronously, so categories overlap in wall time):

| category | s |
|---|---|
| elaboration: elaboration (incl. async proof elaboration) | 156 |
| elaboration: attribute application (the automatic `rfl`-lemma defeq check) | 53.3 |
| elaboration: typeclass inference 12.4, interpretation 2.6, tactic execution 0.2 | 15.2 |
| type checking (kernel) | 7.9 |
| compilation | 0 (not listed) |
| `.olean` serialization | 0.03 |
| other: import 6.7, process pre-definitions 0.2, linting 0.1 | ≈ 7.0 |

## Slow declarations (≥ 30 s)

| declaration | total s | elaboration s | kernel s | classification | note |
|---|---|---|---|---|---|
| `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitTStructure_heart` | 74.0 | 74.0 (skipKernelTC run: 67.4) | < 2 | elaborator defeq check (unfolding the induced `t`-structure) | A `rfl` theorem; the same defeq is decided three times. The attribute step (`applying [<missing>]`, the automatic `rfl`-lemma check) takes 27.0 s, comparing `(constructibleTwoColimitTStructure X l).heart =?= constructibleTwoColimitHeart l X`. Elaborating `rfl` then takes 46.7 s: 24.9 s while `@rfl` is elaborated against the expected type, and 21.7 s for the final check. |
| `AlgebraicGeometry.ProEtale.DerivedCategory.abelian_constructibleTwoColimitHeart` (instance) | 51.6 | 50.3 (skipKernelTC run: 49.7) | < 2 | elaborator defeq check (same problem) | The body `(constructibleTwoColimitTStructure X l).abelianHeart _` has type `Abelian (…TStructure X l).heart.FullSubcategory`. Propagating the expected type `Abelian (constructibleTwoColimitHeart l X).FullSubcategory` re-decides `constructibleTwoColimitHeart l X =?= (…).heart`: 20.9 s, through `LE 0 ⊓ GE 0 =?= le 0 ⊓ ge 0` and `Pi.instMinForall_mathlib`. The same check runs again for 14.6 s. |
| `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitTStructure_ge` | 46.5 | 46.5 (skipKernelTC run: 40.4) | < 2 | elaborator defeq check (same problem) | `rfl` theorem: attribute check 15.6 s plus elaboration of `rfl` 30.5 s (two checks of ≈ 15 s each) of `(…).ge n =?= constructibleTwoColimitGE l X n`. This unfolds `StageSystem.eventually` and `(boundedFieldConstructible E X).tStructure t`. |
| `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTwoColimitTStructure_le` | 36.4 | 36.4 (skipKernelTC run: 36.1) | < 2 | elaborator defeq check (same problem) | Same as `_ge` for the `le` half: attribute check 10.6 s plus elaboration of `rfl` 25.4 s. |

Other declarations ≥ 2 s: `boundedFieldConstructibleStageSystem_assoc_commShift` 2.3 s and `constructibleTwoColimitTStructure` 2.2 s.

Raw output: `….ConstructibleTwoColimitTStructure.profile.txt`, which has the primary run and the skipKernelTC run, trimmed to trace nodes ≥ 1 s.
