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

It follows `dsimp only [completedScalarCounit, completedOrdinaryScalarComplex]`. Profiler: 292 s tactic execution for the call, 0.404 s Kernel check of its declaration. A typed [CounitSorry.lean](probes/CounitSorry.lean) control removes the entire block and falls to 2.92 s wall; it is diagnostic only.

## 3. Structure and mechanism

The profiler-filtered [trace](probes/CounitProfilerOnly.lean) isolates one successful
`Meta.isDefEq` call at 285.339 s inside the `exact`. Its sides are the naturality
equality for `(completedDerivedScalarExtension ...).map (DerivedCategory.Q.map g)`
and the same equality with chosen counit components cast between an
`integralTowerModules` category and its expanded `SheafOfModules` form. The
187.936 s child compares the first composite with and without that cast under
`MorphismProperty.instCategoryLocalization._aux_5`. Its 97.621 s branch reaches
`⋯.choose.1 =?= ⋯.choose.1`; within it, an 89.070 s comparison has two sides
printed identically as `ε.1 ((HomotopyCategory.quotient ...).obj P)`. This
pretty-printing hides distinct chosen-witness/instance paths; the trace does
not justify claiming syntactic identity. A second branch takes 97.401 s and
reaches the same shape at 88.206 s. The repeated deepest call reduces a
`Classical.choose` witness predicate through `LF.IsLeftDerivedFunctor` and
`IsIso (ε.app ...)`. This is an elaborator **definitional-equality / delta
reduction** workload, with the cost centered on chosen counit data.

The three other modules independently show a 286-287 s `Meta.isDefEq` call,
187-188 s and 98-99 s branches, and 88-89 s `ε.1` leaves. The shared inner
shape is therefore confirmed across four modules. No Kernel A-F label applies.

## 4. Confidence and caveats

The phase and inner `Meta.isDefEq` call are **confirmed** by Kernel skip and
the bounded profiler trace. The whole source fails later on a cast/type
mismatch in `simp`, so only the prefix is a valid measured case. An explicit
`trace.Meta.isDefEq` class floods the output even with a profiler threshold;
`trace.profiler true` and threshold 2000 alone retained the slow nested nodes.
