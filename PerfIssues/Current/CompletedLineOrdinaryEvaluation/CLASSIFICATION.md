# CompletedLineOrdinaryEvaluation classification

Case ID / declaration: `WeilConjectures.CompletedLineTensor.counit_naturality`, the private theorem in the derived-square section.
Module: `WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineOrdinaryEvaluation`.
Lean / Mathlib: Lean 4.35.0 and built dependencies; revision `1ef1fddac73e`.
Imports/options: original module imports, one Lean thread, `-DElab.async=false`, profiler threshold 50 ms.

## 1. Phase attribution

Original in-situ file: 326.49 s wall, 325.80 s user CPU, 3,043,108 KB peak RSS. With synchronous Kernel skipping the same source still takes 314.44 s wall and 313.88 s user CPU; its long `exact` remains 298 s. The original profiler attributes 307 s to tactics and 13.7 s to Kernel type checking, including a single 296 s `exact` tactic. This is an elaboration-heavy case under the guide's section 2 gate. The typed `sorry` control below independently isolates the elaboration step.

## 2. Expensive component

The call is:

```lean
with_unfolding_all
  exact homotopyCounit_naturality (completedOrdinaryScalarExtension l E F ι X)
    (completedDerivedScalarExtension l E F ι X)
    ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec
      |>.choose_spec.2.2.choose_spec.choose) g
```

It follows `dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]` in the concrete naturality goal. [CounitNaturalitySorry.lean](probes/CounitNaturalitySorry.lean) replaces only this `with_unfolding_all` block with typed diagnostic `sorry`. The file falls to 30.28 s wall and 10.9 s cumulative tactic time; the 296 s call disappears. The proof term's type check is 0.432 s, so the expensive operation is tactic elaboration of the application. Round 3 identifies the slow `Meta.isDefEq` nesting, though the leaf's hidden instance difference remains undumped.

## 3. Structure and mechanism

The application supplies concrete completed scalar extension functors and a deeply nested witness extracted from `completedScalarChangeData`. A Round 3 same-name run with profiler-filtered Meta tracing finds a 287.140 s `Meta.isDefEq` call, a 188.336 s child, and two `ε.1` comparisons of 89.256 and 89.445 s below `Classical.choose`/`LF.IsLeftDerivedFunctor` data. This matches the other three completed-scalar modules. No Kernel A-F label is assigned.

## 4. Confidence and caveats

The phase, source call, and `Meta.isDefEq` inner comparison shape are **confirmed**. The same-name trace run takes 339.80 user CPU seconds, including tracing overhead; retain 325.80 s as the untraced baseline. The `sorry` copy is diagnostic only. The deepest two sides pretty-print alike, so their exact hidden instance paths remain unresolved.
