# IntegralScalarExtensionConstructible classification

Case ID / declaration: `completedScalarChainComparison_isIso`, private theorem in `IntegralScalarExtensionConstructible`.
Module: `WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible`.
Lean / Mathlib: Lean 4.35.0 with built dependencies; revision `1ef1fddac73e`.
Imports/options: original imports; `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms, and the source's `backward.isDefEq` and `synthInstance.maxSize` options.

## 1. Phase attribution

The complete source takes 226.40 s wall, 225.58 s user CPU, and 2,788,524 KB peak RSS. Kernel skipping takes 211.26 s wall and 210.62 s user CPU while preserving the 196 s `refine`; the original profiler reports about 15.3 s cumulative Kernel checking. Replacing the early `integralScalarExtension_constructible` theorem with `sorry` does not remove the hotspot. Replacing only the later `h2` witness in `completedScalarChainComparison_isIso` with typed `sorry` makes the full source take 29.06 s wall and 28.39 s user CPU. **Phase: elaborator tactic, confirmed.**

## 2. Exact cost site

The expensive declaration is:

```lean
private theorem completedScalarChainComparison_isIso
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hc : IsDerivedCompleteUnrestricted l E Y (DerivedCategory.Q.obj P.obj)) :
    IsIso (DerivedCategory.Q.map ((completedScalarChainComparison l E L ι Y).app P.obj)) := by
  have h := (completedScalarComparison_existsUnique l E L ι Y).exists.choose_spec P
  have h1 : IsIso (...) := ((finiteFreeCompletedScalarComparison l E L ι Y).2.1 _ hc).1
  have h2 : IsIso (completedScalarCounit l E L ι Y P.obj) :=
    (completedScalarChangeData l E L ι Y).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose_spec.2.2 P.obj P.property.1
  ...
```

The staged prefixes isolate the witness. A prefix ending before this theorem takes 11.81 s wall. Including the theorem with its real `h2` takes 210.61 s wall and reports a 197 s `refine`. Retaining only `h` and `h1` takes 13.25 s; adding the real `h2` takes 208.99 s. Replacing only the `h2` RHS with `by sorry` takes 13.12 s. The later `h3`, rewrite, and final `IsIso.of_isIso_comp_left` do not add a comparable cost.

## 3. Mechanism and confidence

The source-level operation is a nested `choose_spec` proof producing an `IsIso` instance for `completedScalarCounit`. The profiler labels the generated tactic as `refine`; the source contains no explicit `refine` in that witness, so the exact inner Meta operation is not identified. The phase and witness location are **confirmed** by the Kernel-skip, staged-prefix, and typed-`sorry` controls. No bounded `Meta.isDefEq` trace, expression pair, instance-path diff, recursor/cast count, or generated proof constant was obtained. The A-F mechanism labels are therefore **unclassified**.

## 4. Caveats

The full source succeeds; copied prefixes and `sorry` controls are diagnostic only. The measured cost includes the concrete dependent types and chosen witnesses in the surrounding declarations. A focused trace of the `h2` witness would be needed to distinguish conversion, reduction, instance synthesis, or dependent-type checking inside the elaborator.
