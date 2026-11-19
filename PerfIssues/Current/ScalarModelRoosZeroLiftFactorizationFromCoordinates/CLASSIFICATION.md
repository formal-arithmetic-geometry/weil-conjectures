# ScalarModelRoosZeroLiftFactorizationFromCoordinates classification

Case ID / declaration: `WeilConjectures.scalarCounit_natural`, the private theorem at the start of the module.
Module: `WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftFactorizationFromCoordinates`.
Lean / Mathlib: 4.35.0 with built dependencies; revision `1ef1fddac73e`.
Imports/options: original imports, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms.

## 1. Phase attribution

The valid [prefix](probes/CounitPrefix.lean) takes 295.17 s wall, 294.31 s user CPU, 2,784,552 KB peak RSS. The identical prefix with `-Ddebug.skipKernelTC=true` takes 296.07 s wall, still with a 293 s `exact`; type checking falls from 0.404 s to 1.19 ms. Thus the hotspot is elaboration, not a Kernel A–F mechanism. The unchanged full module reaches the same call but fails later at line 182; its 303.18 s wall is not a successful whole-module baseline.

## 2. Expensive component

The only `exact` in the valid prefix lies under `with_unfolding_all` in `scalarCounit_natural`:

```lean
exact homotopyCounit_naturality
  (completedOrdinaryScalarExtension.{u, u} l L F j X)
  (completedDerivedScalarExtension.{u, u} l L F j X)
  ((completedScalarChangeData.{u, u} l L F j X).choose_spec.choose_spec.choose_spec
    |>.choose_spec.2.2.choose_spec.choose) g
```

It follows `dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]`. Profiler: 292 s tactic execution for the call, 0.404 s Kernel check of its declaration. The exact inner Meta conversion/WHNF/instance operation remains untraced. A typed [CounitSorry.lean](probes/CounitSorry.lean) control removes the entire block and falls to 2.92 s wall; it is diagnostic only.

## 3. Structure and mechanism

The concrete completed scalar functors and deeply nested scalar-change witness are matched against a general homotopy-counit naturality theorem under full unfolding. This source pattern is identical to the naturality hotspots in `ScalarRoosNaturalityData` and `CompletedScalarOrdinaryCoherence`. The shared pattern is an observation, not proof that a particular Meta conversion is identical in all three runs. No Kernel expression pair, generated `_proof_n`, or DAG metrics are relevantly measured. **Kind: elaborator `exact` under full unfolding; inner operation unclassified.**

## 4. Confidence and caveats

The phase and exact call are **confirmed** by synchronous Kernel skip and the single-call profiler. The whole source fails later on a cast/type mismatch in `simp`, so only the prefix is a valid measured case. A focused bounded `trace.Meta.isDefEq` or elaborator profiler trace would raise confidence about the inner mechanism.
