# NativePullTensor classification

Case ID / family: `exists_nativePullTotalTensor`, `nativePullTotalTensor`, `nativePullTotalTensor_summands`, and `nativeRestrictionDerivedTensor`.
Module: `WeilConjectures.WeilSheaf.Native.NativePullTensor`.
Lean / Mathlib: 4.35.0 with built dependencies; revision `1ef1fddac73e`.
Imports/options: original module imports, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms.

## 1. Phase attribution

Original source: 272.53 s wall, 268.39 s user CPU, 4.15 s system CPU, 7,926,140 KB peak RSS. Synchronous Kernel skip on identical source: 6.99 s wall, 6.16 s user CPU, 2,661,816 KB RSS. Profiler totals: 265 s Kernel type checking versus 0.751 s tactics. **Kernel phase confirmed.** No full async matrix was needed for this synchronous split.

## 2. Exact cost sites

The four checks are 51.5, 80.5, 79.3, and 52.5 s in the declaration order above. The prefix files in `probes/` add declarations in stages and reproduce the same four costs; the final `nativePullTensor` adds no visible >50 ms check. The first theorem applies `NativeRestrictionDescentProof.exists_restrictionTotalSummands` to concrete `upperStar`, `nativeTensorTotal`, summand insertions, and `nativePullSheafTensor`. The next two declarations extract `.choose` and `.choose_spec` from that existential. The final costly definition applies `NativeRestrictionDescentProof.restrictionDerivedOfTotal` to the native tensor models and K-flat localization witness.

In [HotBodiesSorry.lean](probes/HotBodiesSorry.lean), the bodies of these four declarations and the cheap final definition become typed diagnostic `sorry`. Checks of the same declarations still take 48.9, 24.1, 51.1, and 23.7 s respectively; whole-file wall time remains 154.51 s and RSS 6,162,640 KB. Thus substantial cost survives in declaration type/context checking, especially the two existential statements; the real `.choose` and derived-constructor values add further work. Replacing the earlier abstract `restriction_derived_normalization`, `restrictionDerivedOfTotal`, and `restrictionDerivedOfTotal_normalization` bodies with `sorry` leaves the four checks essentially unchanged (51.4, 80.0, 79.4, 52.9 s).

Kernel checking of declared type, value, and final inferred-type reconciliation has not been instrumented as three separate calls. The typed-`sorry` control is evidence for a type/context floor, not a direct timer for `Kernel.check(DeclaredType)`. The exact conversion pair, application prefix, and any generated auxiliary `_proof_n` have not been dumped.

## 3. Structure and mechanism

The expensive statements contain nested concrete functor compositions, natural isomorphisms, K-flat predicates, and object-dependent summand insertions. The `.choose` and `.choose_spec` terms carry dependent existential types. These are candidate representation (E) and dependent-type (C) triggers, but the measured check has not been reduced to an expression pair. `HotBodiesSorry` shows the types remain costly; it does not show which projection or conversion in the Kernel is responsible. No `Expr.equal` test, universe/implicit-argument diff, instance-path diff, recursor/cast count, or shared DAG size was obtained.

## 4. Label, confidence, caveats

Primary mechanism: **unclassified / insufficient expression-level evidence**. E and C are unresolved hypotheses, not assigned labels. Kernel phase and the four declaration cost sites are **confirmed** by the skip control, profiler, and source prefixes. The type/context floor is **strongly supported** by typed-`sorry` controls. A Kernel replay separating declared-type and value checks, followed by an application-prefix/structural diff on the expensive components, would raise confidence. All probes compile the current source prefix; `sorry` and skip are diagnostic and not valid proof results.
