# NativePullTensor classification

Case ID: `exists_nativePullTotalTensor`, `nativePullTotalTensor`, `nativePullTotalTensor_summands`, and `nativeRestrictionDerivedTensor` in `WeilConjectures.WeilSheaf.Native.NativePullTensor`. Lean 4.35.0, master revision `1ef1fddac73e`, built dependencies, one Lean thread, synchronous elaboration.

## 1. Phase gate

The original source takes 268.39 user CPU seconds and 7,926,140 KB peak RSS. With `-Ddebug.skipKernelTC=true`, the same synchronous source takes 6.16 CPU seconds and 2,661,816 KB RSS. Its profiler assigns 265 seconds to Kernel checking and 0.751 seconds to tactics. The four hot declaration checks are 51.5, 80.5, 79.3, and 52.5 seconds respectively. **Kernel phase confirmed.** Skipping the Kernel is diagnostic only.

## 2. Declared type, value, and final conversion

[KernelReplay.lean](probes/KernelReplay.lean) imports the checked module and calls `Kernel.check` separately on each stored declared type and value, then `Kernel.isDefEq` on the inferred and declared types. This is a fresh imported-environment replay, not an in-situ decomposition, but its 239.98 CPU seconds are close to the original 268.39.

| Declaration | Check declared type | Check value | Inferred vs declared conversion |
|---|---:|---:|---:|
| `exists_nativePullTotalTensor` | 23.444 s | 3.082 s | 23.260 s |
| `nativePullTotalTensor` | 0.004 s | 47.457 s | 23.422 s |
| `nativePullTotalTensor_summands` | 23.625 s | 23.459 s | 23.131 s |
| `nativeRestrictionDerivedTensor` | 0.007 s | 23.611 s | 23.285 s |

The type-only [axiom probe](probes/AllTypesOnly.lean) compiles in 54.29 CPU seconds and still has two roughly 24-second checks, while the earlier typed-`sorry` [body probe](probes/HotBodiesSorry.lean) takes 152.56 seconds. Axiom insertion and a theorem with `sorry` take different Kernel paths, so neither is substituted for the direct `Kernel.check` timings above. [SelfVsCross.lean](probes/SelfVsCross.lean) checks the two `nativePullTotalTensor` types against themselves in 0 ms each; their cross-conversion takes 23.167 seconds. Its declared type and value have only 773 and 756 expression objects respectively, so stored size alone does not explain the time.

## 3. Value bisection and conversion pair

[ValuePrefixes.lean](probes/ValuePrefixes.lean) opens the 12 binders of `nativePullTotalTensor` and replays successive application prefixes of `@Exists.choose.{u + 3}`. The type argument checks in 3 ms. Adding the predicate argument requires a 23.050-second conversion between the predicate's inferred `Iso ... -> Prop` type and `Exists.choose`'s expected binder domain; the prefix then checks in 23.475 seconds. Adding the existential proof argument requires a second 22.981-second domain conversion (`exists t, ...` versus `exists a, ...`), and the completed prefix checks in 47.356 seconds. Each new argument checks on its own in at most 6 ms. This locates the value cost in the two **application-domain conversions**, rather than the argument values.

The probe prints bounded prefixes of the `actual type 1` / `expected domain 1` and `actual type 2` / `expected domain 2` pairs with `pp.explicit` and `pp.universes`; `KernelReplay` likewise prints bounded inferred/declared prefixes. [KernelDiff.lean](probes/KernelDiff.lean) walks the full expression pair structurally and prints its first differing subterms. In the slowest declaration's final pair, a generated `nativePullTotalTensor._proof_3` appears where the declared path supplies `CategoryTheory.Sheaf.monoidalPreadditive`; the existence theorem's pair first differs at `Abelian.toPreadditive` versus `Endofunctor.IsoAlgebra.instPreadditive`. The summands pair first differs at `Exists.choose` versus the named `nativePullTotalTensor`. These are first positional differences, not individually timed root causes; the complete cross-expression conversion is timed above.

## 4. Unfolding and mechanism

The in-situ [diagnostics probe](probes/NativeDiagnostics.lean) takes 271.43 CPU seconds and 7,942,652 KB RSS. At the first hot check the Kernel records 1,104,002 `Functor.obj`, 463,500 `Functor.map`, 204,584 `NatTrans.app`, and 129,480 `CategoryStruct.comp` unfolds. The next two checks record about 1.55 million `Functor.obj` unfolds each; `Eq.rec`/`Eq.ndrec` also appear, but no transport-specific conversion was isolated. These counters describe reduction under the expensive `Iso` and existential conversions; a high count for `Functor.obj` alone is not the root cause.

Primary label: **A, Kernel reduction and definitional-equality heavy**. Contributing label: **E, representation/interface mismatch** between the inferred `Exists.choose` application types and the declared concrete functor/instance paths. The costly cross-conversion, cheap self-comparisons, value-prefix jump, structural differences, and repeated concrete-functor unfolding support this assignment. B and C remain possible at individual proof/transport leaves, but the probes do not make either a primary cause.

## 5. Limits

The Kernel API replay imports the completed module, so caches and context differ from the original declaration check. The source-level prefix and typed-placeholder controls reproduce the same four hot declarations, while the replay identifies the internal conversion operations. No library source was modified; axioms, `sorry`, and Kernel skip are diagnostic only.
