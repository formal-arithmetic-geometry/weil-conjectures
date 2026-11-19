# ScalarRoosNaturalityData classification

Case ID / declaration: `WeilConjectures.completedCounitNat`, field `naturality`.
Module: `WeilConjectures.TraceFormula.Scalar.ScalarRoosNaturalityData`.
Lean / Mathlib: Lean 4.35.0 with built project dependencies.
Repository revision: `1ef1fddac73e`.
Imports/options: original module imports; `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms.

## 1. Phase attribution

With synchronous elaboration and Kernel on, the whole module takes 305.94 s wall, 305.03 s user CPU, and 2,826,620 KB peak RSS. Add `-Ddebug.skipKernelTC=true` with the same source: 301.44 s wall, 300.60 s user CPU, and 2,754,752 KB peak RSS. The profiler reports `Lean.Parser.Tactic.exact` at 292 and 297 s respectively, while all Kernel type checking totals 8.61 s on and 2.15 ms skipped. **Conclusion: elaboration/tactic, not a Kernel A–F case.** A full async matrix is unnecessary for this synchronous finding.

## 2. Expensive component

The long call is the `exact` under `with_unfolding_all` in `completedCounitNat.naturality`:

```lean
with_unfolding_all
  exact homotopyCounit_naturality
    (completedOrdinaryScalarExtension.{u, u} l L F j X)
    (completedDerivedScalarExtension.{u, u} l L F j X)
    ((completedScalarChangeData.{u, u} l L F j X).choose_spec.choose_spec.choose_spec
      |>.choose_spec.2.2.choose_spec.choose) f
```

The term is being matched against the naturality equality after `change` and `dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]`. [NaturalitySorry.lean](probes/NaturalitySorry.lean) retains the declaration and those preceding steps, replacing the `with_unfolding_all`/`exact` block with diagnostic `sorry`; wall time falls to 13.17 s and tactic execution to 0.300 s. This isolates the call as the dominant component. The exact inner elaborator operation (`Meta.isDefEq`, WHNF, or instance synthesis) has not been traced, so attributing the 292 s to one of them would be conjecture.

## 3. Structural evidence

The elaborator sees a concrete naturality goal involving `completedDerivedScalarExtension`, `completedScalarCounit`, `completedOrdinaryScalarComplex`, and the nested chosen witness in `completedScalarChangeData`. `with_unfolding_all` exposes those definitions during `exact`. The proof term itself is checked in 0.411 s. No Kernel expression pair, application prefix, generated proof constant, universe/instance diff, recursor, cast count, or shared DAG size is relevantly measured; no A–F label is assigned.

## 4. Mechanism, confidence, caveats

Primary kind: **elaborator tactic `exact` under full unfolding**. The phase and exact source call are **confirmed** by two independent controls. The specific Meta conversion is **unclassified**. A focused `trace.profiler` or `trace.Meta.isDefEq` run on this call would identify its inner operation, if the trace volume is bounded. Measurements are in situ for the original source; the `sorry` control is a copied module and is not a valid proof result. Host contention is limited by the close wall/user CPU values but not independently measured.
