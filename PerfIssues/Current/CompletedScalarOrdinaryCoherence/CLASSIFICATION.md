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

The `exact` call takes 293 s; Kernel checking of the resulting theorem takes 0.423 s. The [probe](probes/CounitNaturalitySorry.lean) replaces only that block with `sorry`, and the 293 s call disappears. This is the exact source-level call and proof application. The inner `Meta.isDefEq` pair, WHNF path, and instance synthesis trace have not been isolated.

## 3. Structural evidence

The concrete arguments are two completed scalar extension functors and a deeply nested witness from `completedScalarChangeData`. The unfolding wrapper permits those definitions to expand during `exact`. Their mere presence does not prove which Meta operation takes the time. No Kernel expression diff, generated `_proof_n`, recursor/cast count, or expression-size measurement was made; A–F labels would overstate the evidence.

## 4. Confidence and caveats

The phase and exact source call are **strongly supported** by profiler and one-block control. The inner elaborator mechanism is **unclassified** pending bounded tracing of `Meta.isDefEq` or `trace.profiler`. The copied `sorry` source is diagnostic only; the original source succeeds.
