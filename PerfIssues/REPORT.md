# Weil performance issues on Lean 4.35.0

This dataset classifies measured declaration costs on the master build tree at revision `1ef1fddac73e` using Lean 4.35.0 and its built Mathlib. The report branch began at `05245385867`; no library source was changed. Runs used `LEAN_NUM_THREADS=1`, `nice -n 10`, `-DElab.async=false`, per-process `timeout` (420-3600 s), and `/usr/bin/time -v`. At most six of our Lean runs overlapped. The host reported 80 logical cores and 308 GiB RAM; the measured jobs were near 100% CPU except for the named high-RSS Kernel checks. Case READMEs report wall time, user CPU, and peak RSS; the shared control table reports user CPU. Kernel skip and `sorry` are diagnostic controls only, never proof results.

The handover's module times came from instruction counts at revision `6f9ee9b2fd1`, not from direct compilation. This table uses direct user CPU seconds at the build-tree revision. A failed whole-module compile is not presented as a successful performance measurement.

## Part A: current modules

| Handover rank / module | User CPU s, measured scope | Top declaration / component | Phase | Exact cost site | Label / confidence | Evidence |
|---|---:|---|---|---|---|---|
| 1 [ProjectiveLineCohomologyChartBoundary](Current/ProjectiveLineCohomologyChartBoundary/CLASSIFICATION.md) | 371.31 full | `chartBoundaryClass_eq`: `exact` 172 s; final existence theorem: `refine` 174 s | Elaborator | general shift-counit identity and concrete supported-class map applications | Not Kernel; source calls confirmed, Meta mechanism open | two independent `sorry` controls, Kernel skip 356.85 CPU s |
| 2 [CompletedLineOrdinaryEvaluation](Current/CompletedLineOrdinaryEvaluation/CLASSIFICATION.md) | 325.80 full | `counit_naturality`: `exact` 296 s | Elaborator | chosen counit components under `Meta.isDefEq`, deepest `ε.1` calls 89.256/89.445 s | Meta definitional equality confirmed | Kernel skip 313.88 CPU s; filtered trace 287.140 s top node |
| 3 [AffineLineConstant](Current/AffineLineConstant/CLASSIFICATION.md) | 295.42 full | integral-model construction: `refine` 56.5 s, `exact` 207 s | Elaborator | nested derived-complete/integral-model witness | Not Kernel; Meta mechanism open | same-name setup replay succeeds |
| 4 [ScalarRoosNaturalityData](Current/ScalarRoosNaturalityData/CLASSIFICATION.md) | 305.03 full | `completedCounitNat.naturality`: `exact` 292 s | Elaborator | chosen counit `ε.1` comparisons, 88.827/88.709 s | Meta definitional equality confirmed | Kernel skip 300.60 CPU s; filtered trace 285.971 s top node |
| 5 [CompletedScalarOrdinaryCoherence](Current/CompletedScalarOrdinaryCoherence/CLASSIFICATION.md) | 304.79 full | `counit_naturality`: `exact` 293 s | Elaborator | chosen counit `ε.1` comparisons, 89.374/89.107 s | Meta definitional equality confirmed | Kernel skip 303.02 CPU s; filtered trace 286.615 s top node |
| 6 [ScalarModelRoosZeroLiftFactorizationFromCoordinates](Current/ScalarModelRoosZeroLiftFactorizationFromCoordinates/CLASSIFICATION.md) | 294.31 valid prefix; whole fails | `scalarCounit_natural`: `exact` 292 s | Elaborator | chosen counit `ε.1` comparisons, 89.070/88.206 s | Meta definitional equality confirmed | valid prefix; filtered trace 285.339 s top node; later `simp` error |
| 7 [IntegralScalarExtensionConstructible](Current/IntegralScalarExtensionConstructible/CLASSIFICATION.md) | 225.58 full | `completedScalarChainComparison_isIso`: nested `h2` witness, profiler `refine` 196 s | Elaborator | `completedScalarChangeData ... choose_spec ...` producing `IsIso (completedScalarCounit ...)` | Not Kernel; witness location confirmed, Meta mechanism open | Kernel skip 210.62 CPU s; typed witness `sorry` 28.39 CPU s |
| 8 [IntegralModelAmbient](Current/IntegralModelAmbient/CLASSIFICATION.md) | 191.41 full | `exists_derivedCompleteIntegers_iso_integralModel_aux`: `refine` 159 s | Elaborator | nested integral-model witness construction | Not Kernel; Meta mechanism open | same-name setup replay succeeds |
| 9 [ProjectionFormulaField](Current/ProjectionFormulaField/CLASSIFICATION.md) | 150.23 full | localizing projection/base-change constructions | Elaborator | repeated concrete localizing-category applications | Not Kernel; Meta mechanism open | same-name setup replay succeeds |
| 10 [NativePullTensor](Current/NativePullTensor/CLASSIFICATION.md) | 268.39 full | `exists_nativePullTotalTensor` 51.5 s; `.choose` 80.5 s; `.choose_spec` 79.3 s; `nativeRestrictionDerivedTensor` 52.5 s | Kernel | `Exists.choose` application-domain conversions (23.05 and 22.98 s); inferred/declared conversion 23.42 s | A primary, E contributing; value prefix and cross conversion timed | Kernel skip 6.16 CPU s; direct type/value replay; 0 ms self versus 23.17 s cross; unfold diagnostics |

The earlier renamed-copy failures for three candidates were measurement artefacts: the original module names plus generated lake setup compile successfully. Their old error logs are retained only as diagnostic context.

## Part B: historical fixes

| Case | Before / After (wall s; peak RSS KB) | Phase | Exact component | Label / confidence | Evidence |
|---|---|---|---|---|---|
| [#1556 AmbientCounterexampleCoproducts](Old/PR1556-AmbientCounterexampleCoproducts/CLASSIFICATION.md) | 60.57; 7,760,464 / 5.73; 3,056,716 | Kernel | final `simpa using h =≫ ...commShiftIso.hom.app` in `not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`, 54.9 s check | A plausible; phase and cost site confirmed | Kernel skip 3.55 s; closing `sorry` 5.66 s |
| [#1563 RawModuleScalarPullback](Old/PR1563-RawModuleScalarPullback/CLASSIFICATION.md) | 117.04; 8,008,236 / 50.98; 5,146,444 | Kernel | `rawModuleScalar_pullback_module_formula`, 68.2 s historical versus 15.2 s fixed check | E plausible, A possible; phase and declaration confirmed | Kernel skip 16.06 s; target `sorry` 57.26 s |
| [#1559 UpperStarMonoidal](Old/PR1559-UpperStarMonoidal/CLASSIFICATION.md) | **Unreproduced on 4.35.0**; PR reports 697 / 140 CPU s and 7.0 / 2.4 GB | Kernel in historical PR measurements; no current phase result | `Functor.OplaxMonoidal.ofLaxSquare` conversion and tensor-comparison application in historical source | E primary, A contributing, source-based | 4.35.0 port failed after API/instance errors; PR controlled measurements only |
| [#1624 IntegersSheafHomologyTower](Old/PR1624-IntegersSheafHomologyTower/CLASSIFICATION.md) | 112.48 s; 11,038,208 KB / 12.44 s; 2,668,464 KB | Kernel | `homologyIntegersTowerIso` final concrete-functor iso chain; target check 102 / 3.18 s | A primary, E contributing; inner pair from historical PR | same-name 4.35.0 before/after values on current prefix |
| [#1625 TensorSheaf component](Old/PR1625-TensorSheaf/CLASSIFICATION.md) | 189.31 s; 8,245,292 KB / 104.95 s; 2,929,672 KB | Kernel | `leftDerivedUpperStarTensorComparison_app_app_fac` proof term; target check 87.6 / 2.43 s | A primary, E contributing; inner pair from historical PR | same-name cut prefixes, raised heartbeat limit; second of two PR changes |
| [#1627 WeilSheafTransport](Old/PR1627-WeilSheafTransport/CLASSIFICATION.md) | 109.17 s; 7,781,816 KB / 9.85 s; 1,837,544 KB | Kernel | `powFunctor` hand-built functor fields and generated laws; three checks 27.8, 55.3, 14.6 s before | E primary, A contributing; inner pair from historical PR | same-name cut prefixes, raised heartbeat limit on both |
| [#1630 PointFiberStageTransitionIso component](Old/PR1630-PointFiberStageTransitionIso/CLASSIFICATION.md) | 185.80 s; 2,624,356 KB / 92.85 s; 2,516,012 KB | Elaborator | `pointFiberStageTransitionIso` old component `exact` 84.8 s | Not Kernel; historical inner pair | same-name full current prefix; final of three PR changes only |
| [#1743 SupportedRestrictionIntegral](Old/PR1743-SupportedRestrictionIntegral/CLASSIFICATION.md) | 580.90 s; 3,729,204 KB / 11.08 s; 3,550,928 KB | Elaborator | `map_supportedRestrictionIntegral_comp` old `refine` 223 s and `exact` 349 s | Not Kernel; historical inner pair | successful cut prefixes; Kernel totals 3.40/3.89 s |
| [#2122 DiagonalTraceFiniteEtaleIntegralBoundary](Old/PR2122-DiagonalTraceFiniteEtaleIntegralBoundary/CLASSIFICATION.md) | 350.32 s; 16,321,824 KB / 30.69 s; 5,285,748 KB | Kernel | old module checks 15.6, 64.3, 176 s versus new 27.2 s | E primary, A contributing; historical pair | successful same-name modules; fixed version imports split helpers |

The [#1557 projection-formula candidate](Old/PR1557-ProjectionFormula/README.md) is excluded: both changed lemmas compile on the current prefix in 4.93 s historical versus 4.51 s fixed, with 3,158,552 versus 3,144,004 KB RSS. This does not reproduce the historical whole-module 10.7-to-4.0 GB drop. No mechanism is asserted for that measurement. All six historical PRs requested in Round 3 were attempted and measured; #1559 remains explicitly unreproduced on 4.35.0.

## Diagnosis paths

### Chart boundary

The module's first 172 s `exact` occurs in `chartBoundaryClass_eq` after unfolding `chartBoundaryClass` and `gysinClass_eq`; it applies `shiftSupportedClass_comp_counit` at concrete zero-locus data. The final existence theorem then spends 174 s elaborating a `refine` whose arguments include `hres`, a `congrArg` over `Θ ≫ ·`, and `map_supportedClassMap_comp_rightDerivedUpperShriekBaseChangeMap_comp_map`. Removing the first call leaves 197.34 CPU s; removing the final refine leaves 191.46 CPU s; removing both gives 17.10 CPU s. Kernel skip preserves both long tactic calls. The exact Meta comparison pairs are not printed, so the internal cause remains open.

### Completed line ordinary evaluation

The 296 s `exact` is in private `counit_naturality`, after `dsimp only` reduces the counit and ordinary scalar complex. It passes the two concrete completed scalar functors and a nested `completedScalarChangeData` witness to `homotopyCounit_naturality`. Replacing only this block with diagnostic `sorry` reduces whole-file user CPU from 325.80 to 29.68 s; Kernel skip still takes 313.88 CPU s. A filtered trace finds a 287.140 s `Meta.isDefEq` call and two approximately 89 s chosen-counit comparisons.

### Scalar Roos naturality

The module's `completedCounitNat.naturality` has the same general theorem application and nested scalar-change witness, here inside a natural-transformation structure field. The sole long `exact` is 292 s and the resulting declaration's Kernel check is 0.411 s. Kernel skipping leaves 297 s in the call, while replacing its block with `sorry` lowers the file to 12.34 CPU s. The filtered trace finds a 285.971 s `Meta.isDefEq` call with chosen-counit `ε.1` leaves at 88.827 and 88.709 s.

### Completed scalar ordinary coherence

The private `counit_naturality` theorem uses `with_unfolding_all` and `exact homotopyCounit_naturality` after reducing the two named scalar constructions. The source also sets `backward.isDefEq.respectTransparency false` locally. The `exact` takes 293 s, with 0.423 s theorem checking. A one-block `sorry` cuts whole-file CPU from 304.79 to 11.37 s; Kernel skip still takes 303.02 s. The filtered trace finds a 286.615 s `Meta.isDefEq` call and two 89 s chosen-counit leaves, matching the other modules.

### Scalar Roos zero-lift factorization

The full file reaches a 292 s `exact` in its first private theorem, `scalarCounit_natural`, then fails at line 182 with `simp made no progress` and a cast/type mismatch. A source prefix ending immediately after the private theorem succeeds and reproduces 292 s in that exact call. Kernel skip on the same valid prefix remains 295.22 CPU s; typed `sorry` drops the prefix to 2.12 CPU s. The filtered trace isolates a 285.339 s `Meta.isDefEq` call, with 187.936 and 97.401 s branches below chosen counit morphisms. The 303.18 s failed full-file run is not a successful module measurement.

### Integral scalar extension constructibility

The complete source compiles in 225.58 user CPU s with one 196 s profiler `refine`; Kernel type checking totals about 15.3 s. Kernel skip still takes 210.62 CPU s and preserves the long refine. Replacing the early `integralScalarExtension_constructible` theorem with `sorry` does not remove it. Staged prefixes identify `completedScalarChainComparison_isIso`: the prefix before it takes 11.81 s, the theorem with its real `h` and `h1` takes 13.25 s, and adding the nested `h2` witness takes 208.99 s. Replacing only that witness with typed `sorry` reduces the full file to 28.39 CPU s. The witness location and elaborator phase are confirmed; the inner Meta operation remains unclassified, so no A–F label is warranted.

### Native pull tensor

The phase gate is 268.39 CPU s on versus 6.16 CPU s with Kernel skipped. Source prefixes add four slow checks: the concrete existential (51.4 s), its `.choose` (about 80 s), `.choose_spec` (about 80 s), and `nativeRestrictionDerivedTensor` (52.2 s). The final `nativePullTensor` is cheap. A direct Kernel API replay of the imported declarations separates type, value, and final conversion. For the slowest `nativePullTotalTensor`, they take 0.004, 47.457, and 23.422 s; the other final conversions each take about 23 s. Self-comparisons of its inferred and declared types take 0 ms, while cross-comparison takes 23.167 s. Bisection of `@Exists.choose` shows two application-domain conversions of 23.050 and 22.981 s; the argument expressions themselves check in at most 6 ms. The actual predicate type and expected binder domain are concrete `Iso ... -> Prop` types with different hidden instance paths. Structural diff of the final pair first meets generated `_proof_3` against `Sheaf.monoidalPreadditive`. In-situ diagnostics count 1.10 million `Functor.obj`, 463,500 `Functor.map`, and 204,584 `NatTrans.app` unfolds in the first hot check. The conversion timings support A as primary and representation mismatch E as contributing; the counts by themselves are not treated as causes.

### Historical #1556

The current prefix with the old one-line `simpa` closing proof compiles in 60.57 s and 7.76 GB, versus 5.73 s and 3.06 GB with the merged `cancel_mono` closing step. The target theorem alone contributes a 54.9 s Kernel check; the `simpa` tactic is below the 50 ms profiler threshold. Kernel skipping reduces the old form to 3.55 s. Replacing only the final `simpa` with `sorry` gives 5.66 s, placing the extra cost in its generated proof term, which whiskers an equality through the concrete comm-shift isomorphism component. The exact internal conversion remains untraced; A is plausible, not confirmed.

### Historical #1563

Both ported forms share today's generic `higherDirectImageRawOverPullback_eq_moduleFactors` helper, which checks in about 32.5 s. The historical target then unfolds concrete functor, raw-pullback, triangle-map, source-factor, and coefficient-factor definitions with `simp only`; it checks in 68.2 s and the file peaks at 8.01 GB. The fixed target applies the helper and checks in 15.2 s, with a 5.15 GB peak. Kernel skip cuts the old file to 16.06 s; typed target `sorry` cuts its check to 21.6 s, showing a nontrivial type/context floor. Concrete versus abstract representation (E) and reduction (A) are plausible; no expression-level pair has separated them.

### Historical #1624

The old `homologyIntegersTowerIso` value, transplanted onto the current module prefix, directly composes named comparison isos over long concrete derived-functor compositions. On 4.35.0 its target Kernel check takes 102 s and the file peaks at 11.04 GB RSS. The current value delegates the final assembly to `homologyIntegersTowerIsoAux` over abstract functors; its target check takes 3.18 s and the file peaks at 2.67 GB RSS. Both forms elaborate in under a second of cumulative tactics. The historical PR separately isolated a single concrete reassociation as a roughly 15 s `rfl` conversion and identified `Functor.comp` unfolding. The direct 4.35.0 before/after control confirms the cost's persistence, while the precise inner expression pair in this toolchain has not been dumped.

### Historical #1625 component

The old direct `Functor.leftDerived₂NatTrans_app_app` proof of `leftDerivedUpperStarTensorComparison_app_app_fac` checks in 87.6 s and peaks the prefix at 8.25 GB RSS. The fixed proof first rewrites the whole natural transformation to the generic construction and checks in 2.43 s, with 2.93 GB RSS. Both forms use the current file prefix, including the first of PR #1625's two fixes, and both needed the same raised heartbeat limit for this historical component form. The PR's diagnosis identifies the pair below the nested `NatTrans.app` projections; this round reproduces the 4.35.0 cost but does not independently dump that inner pair. The remaining 104 s fixed-prefix CPU includes an unchanged 15.4 s Kernel check and other current declarations.

### Historical #1627

The old `powFunctor` value directly constructs a functor from concrete Weil-sheaf and Frobenius-power functors. In a 4.35.0 prefix ending after that definition, its generated field proofs account for three Kernel checks of 27.8, 55.3, and 14.6 s and a 7.78 GB RSS peak. The current application of generic `IsoAlgebra.liftOfStr` removes all three visible checks and peaks at 1.84 GB. The old prefix needs a higher heartbeat limit to finish pending metavariable synthesis; the same limit was used for both timed forms. The historical PR identifies a failed comparison between `frobeniusPowPullback` and `WeilSheaf.frobeniusPullback` that unfolds `adicLowerStar`. That inner pair was not independently re-dumped on 4.35.0, so its mechanism is attributed to the PR diagnosis while our controlled replay establishes persistence of the Kernel cost.

### Historical #1630

The old `pointFiberStageTransitionIso` value's component naturality proof has an 84.8 s `exact`, and the full same-name current-prefix file takes 185.07 user CPU seconds. The fixed `preimageIso` construction takes 92.14 seconds in the same prefix, with only 7-9 seconds of total Kernel checking in either. The historical PR prints the component equality under `rationalStageTransition`, `pointFiberStageEquivalence`, and `β.hom.app`; the 4.35.0 replay confirms the elaborator cost, but isolates only the final of that PR's three changes.

### Historical #1743

The old `map_supportedRestrictionIntegral_comp` on a successful cut prefix takes 579.86 user CPU seconds, almost all in a 223 s `refine` and 349 s `exact`; the current form takes 10.09 seconds. Kernel checking is 3.40 versus 3.89 seconds. The PR diagnoses matching `σ.hom.app` with a named base-change component and then comparing full-subcategory composites at default transparency. The fixed theorem passes equalities of whole morphisms to `map_mateEquiv_app_comp_of_hom_eq` and closes reducibly. The phase and before/after cost reproduce; the inner Meta pair comes from the PR's trace.

### Historical #2122

The old 733-line `DiagonalTraceFiniteEtaleIntegralBoundary` module takes 347.37 user CPU seconds and 16.32 GB peak RSS, with 269 seconds of Kernel checking. The current 133-line module takes 29.87 seconds and 5.29 GB, with a 27.2 s check. The old checks include 15.6, 64.3, and 176 s sites. The PR identifies concrete/abstract category representations under derived-category morphism types, and the fix names the categories and propositions, factors a generic Kummer lemma, and splits helpers into separately built modules. Thus the whole-module difference includes shifted dependency compilation; it is not a single proof-value A/B measurement.

## Observations

### Same-name module replays

The three earlier failed candidates were copied under new filenames. Lean module identity affects private/import-all visibility, `.olean.private` lookup, and scoped attributes. Replaying under the original `WeilConjectures...` path with generated lake setup changed all three outcomes: `AffineLineConstant` 295.42 CPU s, `IntegralModelAmbient` 191.41 s, and `ProjectionFormulaField` 150.23 s, all successful. Their valid profiles are elaboration-heavy, with small Kernel shares. The old failed logs therefore do not support missing-instance claims.

### Shared completed-scalar counit trace

On the valid `scalarCounit_natural` prefix, `trace.profiler true` with threshold 2000 ms retains a 285.339 s `Meta.isDefEq` call inside `exact`. Its sides are the derived scalar functor's naturality equation and a casted version of the same equation using a chosen counit component. A 187.936 s child enters `MorphismProperty.instCategoryLocalization._aux_5`, then `Classical.choose` and `LF.IsLeftDerivedFunctor`; one 89.070 s leaf compares `ε.1 ((HomotopyCategory.quotient ...).obj P)` with the same pretty-printed shape. A second branch of 97.401 s reaches an 88.206 s leaf of the same shape. The apparent identical sides omit hidden arguments, so their printed form does not identify the exact structural difference or prove syntactic identity. Diagnostics count 25,076 `sheafCompose`, 20,624 `Classical.choose`, and 249,887 reducible `Functor.obj` unfolds in this call.

The 187.936-second child has these trimmed sides under the same derived-category composition operation:

```text
(completedDerivedScalarExtension ...).map (DerivedCategory.Q.map g) ≫
  choose.app ((HomotopyCategory.quotient (integralTowerModules ...)).obj B)
=?=
(completedDerivedScalarExtension ...).map (DerivedCategory.Q.map g) ≫
  cast ... (choose.app ((HomotopyCategory.quotient (SheafOfModules ...)).obj B))
```

A separate goal-pair probe elaborates the theorem application without an expected type and prints the first structural differences before conversion: the inferred equality carrier contains `HomotopyCategory.{u+1,u+2,0}` where the goal has `CochainComplex.{u+1,u+2,0} (integralTowerModules ...)`, and the right morphism first differs at `Functor.obj.{u+1,u+2,u+2,u+2}` versus `Functor.obj.{u+2,u+2,u+2,u+2}`. These are concrete positional mismatches in the problem given to `Meta.isDefEq`; neither is individually timed as the 89 s leaf. The probe's concrete theorem is diagnostic `sorry`.

An 80-second-threshold trace with `pp.explicit` finishes in 599.72 user CPU seconds and retains 31 slow `Meta.isDefEq` nodes. Its two deepest `ε.1` calls take 90.455 and 88.496 seconds. Both sides show `ComplexShape.up`; the right side supplies `completedOrdinaryScalarExtension._proof_8` as a proof argument while the left side is printed as `⋯`. Raising the printer depth and step limit still omits the left proof. Enabling `pp.proofs true` expands the left side into a very large proof term, but the printer still truncates it; that run succeeds in 639.91 user CPU seconds. The output does not name the left proof or time that proof argument alone. The extra wall time is dominated by explicit printing.

| Valid-prefix control | User CPU s | Result |
|---|---:|---|
| Baseline `exact` under `with_unfolding_all` | 294.31 | success |
| Same `exact` without `with_unfolding_all` | 294.28 | success |
| Opaque named `have` witness | 14.44 | type mismatch; invalid alternative proof |
| Transparent `let` witness | 295.95 | success |
| `backward.isDefEq.respectTransparency true` | 297.65 | success |
| `backward.isDefEq.respectTransparency false` | 294.57 | success |
| Generic abstract lemma at local variables | 2.31 | lemma succeeds; concrete theorem has diagnostic `sorry` |
| `diagnostics true`, threshold 1000 ms | 297.42 | success |
| Profiler-filtered Meta trace | 303.46 | success; 285.339 s top `isDefEq` node |
| Separate `Meta.synthInstance` trace | 317.77 | success; slowest individual node 8.379 ms |
| Goal-pair explicit structural print | 7.95 | diagnostic `sorry`; first positional differences only |
| Explicit profiler, 80 s threshold | 599.72 | success; 90.455/88.496 s chosen-counit leaves |

The [control sources](Current/ScalarModelRoosZeroLiftFactorizationFromCoordinates/probes/) keep the same prefix. The named `have` is opaque and produces `witness.app`, which does not match the goal's chosen witness; its early error is not a speedup. Removing `with_unfolding_all` and toggling the backward transparency option do not materially change the cost. The abstract lemma shows that matching generic terms is cheap; the concrete chosen data causes the expensive conversion. Explicitly enabling `trace.Meta.isDefEq` prints tiny nodes regardless of `trace.profiler.threshold` in Lean 4.35.0, so the bounded result uses the profiler alone. A separate successful `trace.Meta.synthInstance` run prints 1,171 nodes, with a maximum individual duration of 8.379 ms. An explicit `trace.Meta.whnf` run exceeds its 420-second bound after over 18,000 tiny nodes; that partial run does not exclude aggregate WHNF work. No `Meta.unfold` trace class is registered in Lean 4.35.0; the unfold counts above come from diagnostics.

Three same-name confirmation runs reproduce the nested shape: `ScalarRoosNaturalityData` has a 285.971 s `Meta.isDefEq` node and 88.827/88.709 s `ε.1` leaves; `CompletedLineOrdinaryEvaluation` has 287.140 and 89.256/89.445 s; `CompletedScalarOrdinaryCoherence` has 286.615 and 89.374/89.107 s. All are elaborator definitional-equality/delta reduction at chosen counit data, with no Kernel A-F assignment. These traced runs have printing overhead and do not replace the untraced baselines.

### Historical #1559

The old merge-parent source could not be made into a current-master before benchmark within the 20-minute porting budget: it has an application mismatch and two missing-instance errors after API drift. The PR's controlled measurements are 697 to 140 CPU seconds and 7.0 to 2.4 GB, with target Kernel checks 707 to 42 seconds and 637 to 3.3 seconds. The source diff names the mechanism: `LaxSquareHδ` and `app_app_comp_of_eq` make the equality/commutative-square interface explicit, so the Kernel compares arguments rather than unfolding the whole square. This supports E with A contributing; the failed port is not used as a successful before result.

- Eight current successful modules or valid prefixes exceed 190 whole-file CPU seconds with one or two dominant elaborator tactics. The repeated `homotopyCounit_naturality` application occurs in four independently measured modules or valid prefixes with 292-296 s `exact` calls; their Kernel-skipped controls retain the cost.
- `NativePullTensor` has four separate Kernel checks above 50 s. A direct replay finds approximately 23-second final conversions in each, and the slowest value contains two more approximately 23-second `Exists.choose` argument-domain conversions. Its RSS peaks near 7.93 GB, versus about 2.66 GB when Kernel checking is skipped.
- #1624, #1625, #1627, and #2122 reproduce substantial historical Kernel costs on 4.35.0; #1630 and #1743 reproduce elaboration costs. #1557's isolated changed lemmas do not reproduce its old whole-module memory result.
- The three renamed-copy failures become successful same-name setup replays; their valid profiles are now included in Part A. One current module still fails after a valid first theorem, so its prefix-only status remains recorded.

## Interpretations and limits

- The four completed-scalar naturality calls share the same timed `Meta.isDefEq` nesting down to chosen counit `ε.1` components. Their deepest terms pretty-print alike; an exact hidden-instance diff is still needed before prescribing a source rewrite.
- #1556 and #1563 support the principle that a simpler proof application can reduce Kernel work, but their precise internal conversion sites are not yet dumped. The A/E labels are hypotheses of stated confidence, not root-cause certainties.
- For `NativePullTensor`, the imported-environment replay may have different caches from the original check, but the in-situ profiler, cheap self-comparisons, slow cross-conversion, application-prefix bisection, and unfold counters jointly support the A/E mechanism. The first positional instance/proof mismatch is not asserted to be the sole cause.
- The profiler-filtered scalar trace assigns the dominant time to `Meta.isDefEq` and its delta reductions. Explicit trace-class output remains too noisy for a bounded full run; neither the unfold counts nor the pretty-printed leaf alone establish one individual definition as the cause.
- CPU and wall times are close in the elaborator cases; the native Kernel case has more system time and memory activity. Host load and cache state were not systematically controlled across all runs, so cross-module ordering beyond the large phase distinctions should not be overinterpreted.
