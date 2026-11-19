# CompletedScalarOrdinaryCoherence classification

Case ID / declaration: `WeilConjectures.CompletedLineTensor.counit_naturality`, private theorem in `CounitNaturality` section.
Module: `WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarOrdinaryCoherence`.
Lean / Mathlib: 4.35.0 and built dependencies; revision `1ef1fddac73e`.
Imports/options: original module imports, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms, local `backward.isDefEq.respectTransparency false` as in the source.

## 1. Phase attribution

The complete source compiles in 305.65 s wall, 304.79 s user CPU, 2,729,280 KB peak RSS. With `-Ddebug.skipKernelTC=true` and otherwise identical synchronous settings it still takes 303.85 s wall, and the long `exact` remains 293 s. Profiler totals are 296 s tactics versus 2.01 s type checking. Replacing that block with typed diagnostic `sorry` cuts wall time to 12.15 s and leaves cumulative type checking at 2.02 s. The source-level phase is elaboration, not a Kernel A–F case.

## 2. Expensive component

`counit_naturality` first performs `dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]`, then:

```lean
with_unfolding_all
  exact homotopyCounit_naturality (completedOrdinaryScalarExtension l E F ι X)
    (completedDerivedScalarExtension l E F ι X)
    ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec
      |>.choose_spec.2.2.choose_spec.choose) f
```

The `exact` call takes 293 s; Kernel checking of the resulting theorem takes 0.423 s. The [probe](probes/CounitNaturalitySorry.lean) replaces only that block with `sorry`, and the 293 s call disappears. A Round 3 same-name profiler-filtered trace finds a 286.615 s `Meta.isDefEq` call, a 188.170 s child, and two chosen-counit `ε.1` comparisons of 89.374 and 89.107 s.

## 3. Structural evidence

The slow nested comparison has the same `MorphismProperty.instCategoryLocalization._aux_5`, `Classical.choose`, and `LF.IsLeftDerivedFunctor` shape as the other three completed-scalar modules. The wrapper itself is not the cause: the shared-prefix control without `with_unfolding_all` still takes 294.28 user CPU seconds. No Kernel A-F label applies.

## 4. Confidence and caveats

The phase, source call, and `Meta.isDefEq` inner comparison shape are **confirmed** by the bounded trace. The same-name confirmation takes 323.98 user CPU seconds with tracing overhead; the baseline remains 304.79 s. The deepest two sides pretty-print alike, leaving the hidden instance/witness difference unresolved. The copied `sorry` source is diagnostic only.
