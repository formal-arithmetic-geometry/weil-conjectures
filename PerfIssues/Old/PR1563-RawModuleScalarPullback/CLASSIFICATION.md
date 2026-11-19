# PR #1563 classification: raw pullback module formula

Case ID: PR1563 `AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula`.
Module: `WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula`.
Lean / Mathlib: Lean 4.35.0 with built project dependencies; revision `1ef1fddac73e`.
Imports/options: current module imports, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms.

## 1. Phase attribution

Historical body, Kernel on: 117.04 s wall, 115.92 s user CPU, 8,008,236 KB peak RSS. The same source with `-Ddebug.skipKernelTC=true`: 16.06 s wall, 15.47 s user CPU, 3,048,448 KB RSS. The fixed body: 50.98 s wall, 50.00 s user CPU, 5,146,444 KB RSS. The cost difference is Kernel checking, with an elaboration floor of roughly 15 s for the historical `simp`.

## 2. Expensive operation

The per-declaration profiler gives 68.2 s of target type checking with the historical body versus 15.2 s with the fixed body. The shared helper takes 32.4-32.7 s in both forms. Replacing the target body with typed diagnostic `sorry` in [TargetSorry.lean](probes/TargetSorry.lean) gives 21.6 s on its target and 57.26 s whole-file wall. This places a large part of the historical cost in the proof value, while also showing a nontrivial declared-type/context floor. Type checking of declared type, proof value, and final inferred-type conversion were not separately replayed.

The historical closing proof unfolds the concrete functor and factor definitions under `simp only`, then closes by `rfl`:

```lean
simp only [higherDirectImageRawOverFunctor, higherDirectImageRawOverPullbackHom_apply,
  higherDirectImageRawOverPullback, higherDirectImageRawTrianglePullback,
  rawTriangleMap, moduleSourceFactor, rawTriangleSource,
  moduleCoefficientFactor, Category.assoc]; rfl
```

The fixed form applies `higherDirectImageRawOverPullback_eq_moduleFactors Λ k G q U f z`, a separate theorem stated over the raw pullback instead of the functor's `op B` component. The current helper in turn applies `rawTriangleMap_whiskerLeft_eq_comp` over abstract categories. The actual elaborated Kernel conversion pair and first expensive application prefix have not been dumped.

## 3. Structural evidence

The source-level difference is concrete functor unfolding through `higherDirectImageRawOverFunctor` and `unop (op B)` versus an abstract helper and direct raw-pullback statement. The same target type and imports are used in both real forms; Kernel skip collapses their check. The target-`sorry` control removes the historical proof term and lowers the check, but also changes Kernel context/caching. No `Expr.equal` result, universe/instance diff, `_proof_n` comparison, recursor/cast count, or shared DAG size is available.

## 4. Mechanism, confidence, caveats

Primary label: **E, plausible**, concrete functor representation versus a raw-pullback helper; **A** is a plausible contributor because the historical proof unfolds multiple concrete definitions. Kernel phase and target declaration are **confirmed**. The exact internal conversion pair and A/E causal split are **unclassified** until replay or expression dumping. This port retains current generic helpers and does not claim to reproduce the historical 11.8-to-7.5 GB whole-module result; its controlled target change gives 8.01-to-5.15 GB here. Diagnostic `sorry` and Kernel skip are not valid proofs.
