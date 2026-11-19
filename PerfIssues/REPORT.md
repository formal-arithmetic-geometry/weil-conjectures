# Weil performance issues on Lean 4.35.0

This dataset classifies measured declaration costs on the master build tree at revision `1ef1fddac73e` using Lean 4.35.0 and its built Mathlib. The report branch began at `05245385867`; no library source was changed. Runs used `LEAN_NUM_THREADS=1`, `nice -n 10`, `-DElab.async=false`, per-process `timeout` (900-3600 s), and `/usr/bin/time -v`. At most six of our Lean runs overlapped. The host reported 80 logical cores and 308 GiB RAM; the measured jobs were near 100% CPU except for the named high-RSS Kernel checks. Wall, user CPU, system CPU, and peak RSS are retained in each README. Kernel skip and `sorry` are diagnostic controls only, never proof results.

The handover's module times came from instruction counts at revision `6f9ee9b2fd1`, not from direct compilation. This table uses direct user CPU seconds at the build-tree revision. A failed whole-module compile is not presented as a successful performance measurement.

## Part A: current modules

| Rank / module | User CPU s, measured scope | Top declaration / component | Phase | Exact cost site | Label / confidence | Evidence |
|---|---:|---|---|---|---|---|
| 1 [ProjectiveLineCohomologyChartBoundary](Current/ProjectiveLineCohomologyChartBoundary/CLASSIFICATION.md) | 371.31 full | `chartBoundaryClass_eq`: `exact` 172 s; final existence theorem: `refine` 174 s | Elaborator | general shift-counit identity and concrete supported-class map applications | Not Kernel; source calls confirmed, Meta mechanism open | two independent `sorry` controls, Kernel skip 356.85 CPU s |
| 2 [CompletedLineOrdinaryEvaluation](Current/CompletedLineOrdinaryEvaluation/CLASSIFICATION.md) | 325.80 full | `counit_naturality`: `exact` 296 s | Elaborator | `homotopyCounit_naturality` with completed scalar functors and chosen witness under `with_unfolding_all` | Not Kernel; source call confirmed, Meta mechanism open | Kernel skip 313.88 CPU s; one-block `sorry` 29.68 CPU s |
| 3 [AffineLineConstant](Current/AffineLineConstant/CLASSIFICATION.md) | 295.42 full | integral-model construction: `refine` 56.5 s, `exact` 207 s | Elaborator | nested derived-complete/integral-model witness | Not Kernel; Meta mechanism open | same-name setup replay succeeds |
| 4 [ScalarRoosNaturalityData](Current/ScalarRoosNaturalityData/CLASSIFICATION.md) | 305.03 full | `completedCounitNat.naturality`: `exact` 292 s | Elaborator | `homotopyCounit_naturality` under `with_unfolding_all` | Not Kernel; source call confirmed, Meta mechanism open | Kernel skip 300.60 CPU s; one-block `sorry` 12.34 CPU s |
| 5 [CompletedScalarOrdinaryCoherence](Current/CompletedScalarOrdinaryCoherence/CLASSIFICATION.md) | 304.79 full | `counit_naturality`: `exact` 293 s | Elaborator | same general naturality theorem at concrete scalar functors | Not Kernel; source call confirmed, Meta mechanism open | Kernel skip 303.02 CPU s; one-block `sorry` 11.37 CPU s |
| 6 [ScalarModelRoosZeroLiftFactorizationFromCoordinates](Current/ScalarModelRoosZeroLiftFactorizationFromCoordinates/CLASSIFICATION.md) | 294.31 valid prefix; whole fails | `scalarCounit_natural`: `exact` 292 s | Elaborator | `homotopyCounit_naturality` under `with_unfolding_all` | Not Kernel; prefix call confirmed, Meta mechanism open | valid prefix, Kernel skip 295.22 CPU s, `sorry` 2.12 CPU s; later `simp` error |
| 7 [IntegralScalarExtensionConstructible](Current/IntegralScalarExtensionConstructible/CLASSIFICATION.md) | 225.58 full | `completedScalarChainComparison_isIso`: nested `h2` witness, profiler `refine` 196 s | Elaborator | `completedScalarChangeData ... choose_spec ...` producing `IsIso (completedScalarCounit ...)` | Not Kernel; witness location confirmed, Meta mechanism open | Kernel skip 210.62 CPU s; typed witness `sorry` 28.39 CPU s |
| 8 [IntegralModelAmbient](Current/IntegralModelAmbient/CLASSIFICATION.md) | 191.41 full | `exists_derivedCompleteIntegers_iso_integralModel_aux`: `refine` 159 s | Elaborator | nested integral-model witness construction | Not Kernel; Meta mechanism open | same-name setup replay succeeds |
| 9 [ProjectionFormulaField](Current/ProjectionFormulaField/CLASSIFICATION.md) | 150.23 full | localizing projection/base-change constructions | Elaborator | repeated concrete localizing-category applications | Not Kernel; Meta mechanism open | same-name setup replay succeeds |
| 10 [NativePullTensor](Current/NativePullTensor/CLASSIFICATION.md) | 268.39 full | `exists_nativePullTotalTensor` 51.5 s; `.choose` 80.5 s; `.choose_spec` 79.3 s; `nativeRestrictionDerivedTensor` 52.5 s | Kernel | checking four concrete existential/derived comparison declarations | Unclassified; type/context floor strongly supported | Kernel skip 6.16 CPU s; staged prefixes; five-body `sorry` still 152.56 CPU s |

The earlier renamed-copy failures for three candidates were measurement artefacts: the original module names plus generated lake setup compile successfully. Their old error logs are retained only as diagnostic context.

## Part B: historical fixes

| Case | Before / After (wall s; peak RSS KB) | Phase | Exact component | Label / confidence | Evidence |
|---|---|---|---|---|---|
| [#1556 AmbientCounterexampleCoproducts](Old/PR1556-AmbientCounterexampleCoproducts/CLASSIFICATION.md) | 60.57; 7,760,464 / 5.73; 3,056,716 | Kernel | final `simpa using h =≫ ...commShiftIso.hom.app` in `not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`, 54.9 s check | A plausible; phase and cost site confirmed | Kernel skip 3.55 s; closing `sorry` 5.66 s |
| [#1563 RawModuleScalarPullback](Old/PR1563-RawModuleScalarPullback/CLASSIFICATION.md) | 117.04; 8,008,236 / 50.98; 5,146,444 | Kernel | `rawModuleScalar_pullback_module_formula`, 68.2 s historical versus 15.2 s fixed check | E plausible, A possible; phase and declaration confirmed | Kernel skip 16.06 s; target `sorry` 57.26 s |
| [#1559 UpperStarMonoidal](Old/PR1559-UpperStarMonoidal/CLASSIFICATION.md) | 217.50 failed port; historical 697 / 140 CPU s and 7.0 / 2.4 GB | Kernel | `Functor.OplaxMonoidal.ofLaxSquare` conversion and tensor-comparison application | E primary, A contributing | current port stopped after API/instance errors; PR controlled measurements |

The [#1557 projection-formula candidate](Old/PR1557-ProjectionFormula/README.md) is excluded: both changed lemmas compile on the current prefix in 4.93 s historical versus 4.51 s fixed, with 3,158,552 versus 3,144,004 KB RSS. This does not reproduce the historical whole-module 10.7-to-4.0 GB drop. We stopped after these cheap isolated forms; no mechanism is asserted for the old measurement. The remaining marked historical PRs were not ported, so this table does not claim coverage of all ten.

## Diagnosis paths

### Chart boundary

The module's first 172 s `exact` occurs in `chartBoundaryClass_eq` after unfolding `chartBoundaryClass` and `gysinClass_eq`; it applies `shiftSupportedClass_comp_counit` at concrete zero-locus data. The final existence theorem then spends 174 s elaborating a `refine` whose arguments include `hres`, a `congrArg` over `Θ ≫ ·`, and `map_supportedClassMap_comp_rightDerivedUpperShriekBaseChangeMap_comp_map`. Removing the first call leaves 197.34 CPU s; removing the final refine leaves 191.46 CPU s; removing both gives 17.10 CPU s. Kernel skip preserves both long tactic calls. The exact Meta comparison pairs are not printed, so the internal cause remains open.

### Completed line ordinary evaluation

The 296 s `exact` is in private `counit_naturality`, after `dsimp only` reduces the counit and ordinary scalar complex. It passes the two concrete completed scalar functors and a nested `completedScalarChangeData` witness to `homotopyCounit_naturality` under `with_unfolding_all`. Replacing only this block with diagnostic `sorry` reduces whole-file user CPU from 325.80 to 29.68 s; Kernel skip still takes 313.88 CPU s and the exact remains 298 s. The proof term checks in 0.432 s. The source call is isolated, while the particular Meta conversion or unfolding path is not.

### Scalar Roos naturality

The module's `completedCounitNat.naturality` has the same general theorem application and nested scalar-change witness, here inside a natural-transformation structure field. The sole long `exact` is 292 s and the resulting declaration's Kernel check is 0.411 s. Kernel skipping leaves 297 s in the call, while replacing its block with `sorry` lowers the file to 12.34 CPU s. This directly establishes the elaborator phase. Neither the profiler nor the controls distinguish `Meta.isDefEq`, WHNF, or instance search inside the tactic.

### Completed scalar ordinary coherence

The private `counit_naturality` theorem uses `with_unfolding_all` and `exact homotopyCounit_naturality` after reducing the two named scalar constructions. The source also sets `backward.isDefEq.respectTransparency false` locally. The `exact` takes 293 s, with 0.423 s theorem checking. A one-block `sorry` cuts whole-file CPU from 304.79 to 11.37 s; Kernel skip still takes 303.02 s. The shared source pattern with the two Roos cases is visible, but no common inner Meta pair has been demonstrated.

### Scalar Roos zero-lift factorization

The full file reaches a 292 s `exact` in its first private theorem, `scalarCounit_natural`, then fails at line 182 with `simp made no progress` and a cast/type mismatch. A source prefix ending immediately after the private theorem succeeds and reproduces 292 s in that exact call. Kernel skip on the same valid prefix remains 295.22 CPU s; typed `sorry` drops the prefix to 2.12 CPU s. This is a valid declaration-level elaboration case, but the 303.18 s failed full-file run is not a successful module measurement. The inner Meta operation is still untraced.

### Integral scalar extension constructibility

The complete source compiles in 225.58 user CPU s with one 196 s profiler `refine`; Kernel type checking totals about 15.3 s. Kernel skip still takes 210.62 CPU s and preserves the long refine. Replacing the early `integralScalarExtension_constructible` theorem with `sorry` does not remove it. Staged prefixes identify `completedScalarChainComparison_isIso`: the prefix before it takes 11.81 s, the theorem with its real `h` and `h1` takes 13.25 s, and adding the nested `h2` witness takes 208.99 s. Replacing only that witness with typed `sorry` reduces the full file to 28.39 CPU s. The witness location and elaborator phase are confirmed; the inner Meta operation remains unclassified, so no A–F label is warranted.

### Native pull tensor

The phase gate is opposite to the preceding cases: 268.39 CPU s on versus 6.16 CPU s with Kernel skipped. Source prefixes add four slow checks: the concrete `exists_nativePullTotalTensor` existential (51.4 s), its `.choose` (about 80 s), `.choose_spec` (about 80 s), and `nativeRestrictionDerivedTensor` (52.2 s). The final `nativePullTensor` itself is cheap. Replacing five later bodies with typed `sorry` still leaves 152.56 CPU s and large checks on the two existential statements, showing a type/context floor; real values add further time. No separate `Kernel.check(DeclaredType)` replay or exact conversion pair is available, so C/E remain hypotheses rather than labels.

### Historical #1556

The current prefix with the old one-line `simpa` closing proof compiles in 60.57 s and 7.76 GB, versus 5.73 s and 3.06 GB with the merged `cancel_mono` closing step. The target theorem alone contributes a 54.9 s Kernel check; the `simpa` tactic is below the 50 ms profiler threshold. Kernel skipping reduces the old form to 3.55 s. Replacing only the final `simpa` with `sorry` gives 5.66 s, placing the extra cost in its generated proof term, which whiskers an equality through the concrete comm-shift isomorphism component. The exact internal conversion remains untraced; A is plausible, not confirmed.

### Historical #1563

Both ported forms share today's generic `higherDirectImageRawOverPullback_eq_moduleFactors` helper, which checks in about 32.5 s. The historical target then unfolds concrete functor, raw-pullback, triangle-map, source-factor, and coefficient-factor definitions with `simp only`; it checks in 68.2 s and the file peaks at 8.01 GB. The fixed target applies the helper and checks in 15.2 s, with a 5.15 GB peak. Kernel skip cuts the old file to 16.06 s; typed target `sorry` cuts its check to 21.6 s, showing a nontrivial type/context floor. Concrete versus abstract representation (E) and reduction (A) are plausible; no expression-level pair has separated them.

## Observations

### Same-name module replays

The three earlier failed candidates were copied under new filenames. Lean module identity affects private/import-all visibility, `.olean.private` lookup, and scoped attributes. Replaying under the original `WeilConjectures...` path with generated lake setup changed all three outcomes: `AffineLineConstant` 295.42 CPU s, `IntegralModelAmbient` 191.41 s, and `ProjectionFormulaField` 150.23 s, all successful. Their valid profiles are elaboration-heavy, with small Kernel shares. The old failed logs therefore do not support missing-instance claims.

### Shared completed-scalar counit trace

The valid `scalarCounit_natural` prefix was traced with `trace.Meta.isDefEq`, profiler, and diagnostics controls. The trace printed many small instance-oriented comparisons (`Field`, `Algebra`, `Semiring`, and stuck synthesis metavariables) and repeated transparency raises; a full trace exceeded the bounded run before one dominant conversion could be isolated. This confirms that the repeated `with_unfolding_all` application is an aggregate Meta workload, but it does not justify choosing WHNF, instance search, or one conversion pair as the mechanism. The four completed-scalar modules remain **Not Kernel; Meta mechanism open**.

### Historical #1559

The old merge-parent source could not be made into a current-master before benchmark within the 20-minute porting budget: it has an application mismatch and two missing-instance errors after API drift. The PR's controlled measurements are 697 to 140 CPU seconds and 7.0 to 2.4 GB, with target Kernel checks 707 to 42 seconds and 637 to 3.3 seconds. The source diff names the mechanism: `LaxSquareHδ` and `app_app_comp_of_eq` make the equality/commutative-square interface explicit, so the Kernel compares arguments rather than unfolding the whole square. This supports E with A contributing; the failed port is not used as a successful before result.

- Six current successful modules or valid prefixes spend over 190 CPU seconds in one or two elaborator tactics, and their synchronous Kernel-skipped controls retain those calls. The repeated `homotopyCounit_naturality` application occurs in three independently measured modules with 292-296 s `exact` calls.
- `NativePullTensor` has four separate Kernel checks above 50 s, and even typed-`sorry` replacements leave a 153 s file. Its RSS peaks near 7.93 GB, versus about 2.66 GB when Kernel checking is skipped.
- Two historical proof forms reproduce large Kernel cost reductions on 4.35.0. #1557's isolated changed lemmas do not reproduce its old whole-module memory result.
- The three renamed-copy failures become successful same-name setup replays; their valid profiles are now included in Part A. One current module still fails after a valid first theorem, so its prefix-only status remains recorded.

## Interpretations and limits

- The repeated completed-scalar naturality source pattern is a candidate shared elaborator problem. No bounded inner Meta trace was obtained, so this report does not claim a single common conversion pair or prescribe a source fix.
- #1556 and #1563 support the principle that a simpler proof application can reduce Kernel work, but their precise internal conversion sites are not yet dumped. The A/E labels are hypotheses of stated confidence, not root-cause certainties.
- For `NativePullTensor`, large concrete/dependent theorem types and chosen components are visible, but type size or dependence alone is not causal evidence. Its mechanism remains unclassified until a declared-type/value replay and structural expression comparison are performed.
- The scalar counit trace demonstrates how quickly a full Meta trace becomes noisy: it is evidence about workload shape, not a causal assignment to a particular Meta subsystem.
- CPU and wall times are close in the elaborator cases; the native Kernel case has more system time and memory activity. Host load and cache state were not systematically controlled across all runs, so cross-module ordering beyond the large phase distinctions should not be overinterpreted.
