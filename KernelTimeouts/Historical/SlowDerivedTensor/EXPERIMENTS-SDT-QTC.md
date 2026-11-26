# Slow Derived Tensor: D/D' and Q/Qh transport cost (round 10b)

## Evidence and method

**[Direct root evidence]** is a new READY4.2 trace of the original twelve-binder inferred-versus-stored `icd_tensorObj_probe` equality. **[Direct child replay]** is a new check of an Expr extracted from that root. **[API/source evidence]** is the pinned declaration or source. **[Counterfactual]** changes arguments in a Kernel-checked diagnostic and therefore changes the M0 obligation. **[Inference]** interprets those observations. **[Unknown]** marks a measurement or control not obtained. These labels apply to each table row and conclusion below.

The pinned revisions are Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11cda51a86af692955474`, and consumer `bdab171985a`. The investigation ran on the measurement server in a private copy under `sdt-qtc/`, with READY4.2 observational Kernel instrumentation, one Lean process for this investigation at a time, and a 3600 s limit per invocation. No semantic Kernel or typeclass-search code was changed. Disk stayed at 84%. **[Direct root evidence; API/source evidence]**

The original root trace is `sdtqtc/qtc-root.trace`, the exact stage replays are `sdtqtc/qtc-stage-details.txt` and `sdtqtc/qtc-stage.counters`, the `map_comp` trace is `sdtqtc/qtc-map-comp.trace`, and the pinned declaration export is `sdtqtc/qtc-declarations.txt`. The root/child replays overlap; their inclusive times must not be added. **[Direct root evidence; Direct child replay]**

## 1. Exact functors and types (Experiment A, P1)

| Declaration | Domain and target | Object/morphism construction | Relationship | Evidence |
|---|---|---|---|---|
| `CategoryTheory.MorphismProperty.Q W` (raw `Q0`) | `C ⥤ W.Localization` | `Quotient.functor` after paths/`psi1`; map is quotient class | Raw localization stage for the *complex* source, not a map on the measured K pair | **[API/source evidence]** |
| `DerivedCategory.Q` | `CochainComplex C Int ⥤ DerivedCategory C` | Alias to `HomologicalComplexUpToQuasiIso.Q`, which uses the selected `HasLocalization.L`; selected L composes a localization with `ShrinkHoms.equivalence.functor` | Distinct constant and domain from `Qh` | **[API/source evidence]** |
| `DerivedCategory.Qh` | `HomotopyCategory C (.up Int) ⥤ DerivedCategory C` | Alias to `HomologicalComplexUpToQuasiIso.Qh := CategoryTheory.Quotient.lift _ Q ...` | The exact functor on the K-level pair | **[API/source evidence; Direct child replay]** |
| `CategoryTheory.toDerivedMonoidal Qh W` (`toD'`) | K `⥤ DerivedMonoidal Qh W` | Definition is literally the supplied functor `L`; object and map fields are reused | Definitionally the same map as `Qh` after exposing the target alias | **[API/source evidence]** |

The pinned locations are `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean:87-115`, `Mathlib/Algebra/Homology/Localization.lean:175-184`, `Mathlib/CategoryTheory/Localization/Construction.lean:112-116`, `Mathlib/CategoryTheory/Localization/HasLocalization.lean:73`, `Mathlib/CategoryTheory/Localization/LocallySmall.lean:37-44`, `Mathlib/CategoryTheory/Quotient.lean:241-245`, `Mathlib/CategoryTheory/EssentiallySmall.lean:152-175`, and `WeilConjectures/FromJoel/CategoryTheory/Monoidal/Derived.lean:35-39`. The elaborated types and values, including universes, are exported in `sdtqtc/qtc-declarations.txt`. **[API/source evidence]**

`DerivedCategory.Q` and `Qh` are not definitionally equal functors because their source categories differ. The pinned `quotientCompQhIso` gives `HomotopyCategory.quotient C (.up Int) ⋙ Qh ≅ Q`; it relates different stages after a domain-changing quotient. There is no direct, type-correct `Q.map m` for the measured K-level morphism `m`. **[API/source evidence]**

`D' := DerivedMonoidal Qh W` reduces to `D`; `instCategoryDerivedMonoidal` delegates to `Category D`. The target Hom is `Shrink (Quot (HomRel.CompClosure ...))` under the selected `ShrinkHoms` category. One `equivShrink` layer is the selected representation, not by itself redundant wrapping. **[API/source evidence]**

## 2. Production path and transport lineage (Experiments A, C, F; P3, P6)

The measured path is `whiskerRight`-derived K morphism -> `Qh.map`/`toDerivedMonoidal.map` -> `CategoryTheory.Quotient.lift` -> `Quot.liftOn` of the K representative -> the selected localization's quotient Hom -> `ShrinkHoms.equivalence.functor`/`equivShrink` -> target Hom and composition. `Q` is the complex-level functor supplied to `Qh`'s lift, not a second map applied to a K-level output. **[API/source evidence; Direct child replay; Inference]**

The two extracted children of `uncurry.map` are `NatTrans.app` and `Functor.map`. Each weak-head reduces to `Quot.lift/6`; its last argument is respectively a K-level `NatTrans.app/8` and K-level `Functor.map/8`. Their inferred source Hom types compare successfully. No `Qh.map (Q.map m)` occurs in these extracted outputs; the two functors' domains would also prevent that expression for this K pair. **[Direct child replay; API/source evidence]**

| Same original root branch | Calls | Non-overlapping subtree exclusive time | Evidence |
|---|---:|---:|---|
| Full equality root | 6,267,702 | 58.166 s | **[Direct root evidence]** |
| `U.map` | selected branch | 17.465 s | **[Direct root evidence]** |
| `U.map_comp` | selected branch | 39.334 s | **[Direct root evidence]** |
| Other root branches | not separately resolved | 1.367 s residual | **[Direct root evidence; Inference]** |

The whole-root reduction counters are `DerivedCategory.Qh`: 2 unfolds / 0.007 ms; `CategoryTheory.Quotient.lift`: 18 / 0.075 ms; `Quot.liftOn`: 58 / 0.013 ms; `ShrinkHoms.equivalence`: 1 / 0.023 ms; `ShrinkHoms.functor`: 1 / 0.017 ms; `CategoryStruct.comp`: 202,217 / 16.679 ms. These count dynamic delta reductions throughout 6.27 million recursive calls, not 18 independent quotient transports. **[Direct root evidence]**

The trace records root ID 1193 and call ID/parent/depth for its selected expensive calls. The trace's 40-path summary and top-child list do not enumerate every reduction's exact pre/post Expr, sharing identity, or every quotient/shrink call ID. An exact non-overlapping semantic split of the 58.166 s into source, quotient lift, shrink conversion, and target Hom descendants is therefore unavailable. **[Direct root evidence; Unknown]**

## 3. Same-pair before and after transport (Experiment B, P2)

The source and target checks below use the exact same extracted K morphism pair within each numbered child. The outer pair's heads are `NatTrans.app/8`, its source Hom is `Quiver.Hom/4`, and its output reduces to `Quot.lift/6`; the inner pair's heads are `Functor.map/8` with the same source-Hom shape. The outer source expression sizes without sharing are 57,425 / 23,615 nodes. Both source Hom types compare. **[Direct child replay]**

| Stage / exact pair | Kernel result | Calls | READY4.2 exclusive time | Wall time | Evidence |
|---|---|---:|---:|---:|---|
| Outer K morphisms `mL ≟ mR` | true | 1,734,062 | 12.914 s | 14.518 s | **[Direct child replay]** |
| Outer `Qh`/`toD'` outputs | true | 1,846,115 | 13.768 s | 15.497 s | **[Direct child replay]** |
| Outer source Hom types | true | 111,960 | 0.673 s | 0.744 s | **[Direct child replay]** |
| Inner K morphisms | true | about 112,000 | 0.664-0.673 s | 0.743 s | **[Direct child replay]** |
| Inner `Qh`/`toD'` outputs | true | about 112,000 | 0.672 s | 0.739 s | **[Direct child replay]** |
| Raw `Q0.map` and `DerivedCategory.Q.map` on these K morphisms | ill-typed | N/A | N/A | N/A | **[API/source evidence]** |

The first printed structural difference of the full map output is the universe-instantiated `HomotopyCategory.quasiIso` under the source provider; the two K morphism representations also carry different monoidal-provider arguments. The outer source pair is already expensive, and its transported output adds about 0.854 s in this child-replay mode. That difference is diagnostic, not an additive same-root transport charge. **[Direct child replay; Inference]**

## 4. Target Hom, object, and category controls (Experiment D, P4)

| Check | Result | Wall time | M0 changed? | Evidence |
|---|---|---:|---|---|
| Original map body | true | 16.096 s | No, exact extracted child | **[Direct child replay]** |
| Original target Hom type | true | 0.741 s | No, exact extracted type | **[Direct child replay]** |
| Share both map morphism arguments; keep target objects | true, Kernel-valid | 1.143 s | Yes | **[Counterfactual]** |
| Share map morphisms and objects | true, Kernel-valid | below 1 ms resolution | Yes | **[Counterfactual]** |
| Share target objects only; retain source-derived morphisms | true, Kernel-valid | 13.227 s | Yes | **[Counterfactual]** |
| Target Hom type with shared endpoints | true, Kernel-valid | below 1 ms resolution | Yes | **[Counterfactual]** |
| Target Hom type with only category argument shared | true, Kernel-valid | 0.622 s | Yes | **[Counterfactual]** |

The shared-morphism residual requires unequal endpoint context; sharing Hom endpoints removes its selected Hom-type cost. The same selected category declaration appears on both original sides, with different source-derived arguments. The `ShrinkHoms` `Small` witness is part of forming the Hom type, but its own exclusive cost was not separately measured. **[Counterfactual; Direct child replay; API/source evidence; Unknown]**

## 5. `map_comp` and RHS controls (Experiment E, P5)

The proposition is `Eq (target Hom) (U.map (f ≫ g)) (U.map f ≫ U.map g)` after five pointer-shared binder domains. The proof is skipped by proof irrelevance; the target-Hom carrier and equality endpoints are compared. The RHS contains two structurally distinct uncurried map expressions. **[Direct child replay; Direct root evidence]**

| Disjoint path in original root's `map_comp` branch | Exclusive subtree time | Evidence |
|---|---:|---|
| Equality carrier/domains/other residual | 1.195 s | **[Direct root evidence; Inference]** |
| LHS mapped composite | 17.402 s | **[Direct root evidence]** |
| RHS target composition and its two maps | 20.737 s | **[Direct root evidence]** |
| Total `map_comp` | 39.334 s | **[Direct root evidence]** |

A separate direct `map_comp` trace replay took 39.703 s / 4,196,946 calls. In the trace, the disjoint LHS and RHS branches took 16.502 s and 22.399 s. Under the RHS branch, the two distinct map-argument paths took 8.768 s and 13.632 s. The fixed READY4.2 counter replay measured a 37.501 s conclusion and RHS controls of first-shared 16.525 s, second-shared 16.373 s, both-shared 1.230 s, and objects-shared 28.773 s. These paths are non-overlapping within their respective replays. Differences between root and child-replay numbers reflect separate cache/timing contexts and must not be summed. **[Direct child replay; Counterfactual]**

The type-correct RHS controls share first map, second map, both maps, or target objects. Each changes M0 and is diagnostic. Their READY4.2 counters are recorded in `sdtqtc/qtc-map-comp-controls.counters`; a valid single shared-map control cannot remove the other source-derived map, whereas sharing both removes most of the RHS comparison. **[Counterfactual; Inference]**

## 6. D/D' and Q/Qh hypothesis tests (Experiment F, P6)

| Hypothesis | Result | Evidence |
|---|---|---|
| H1: unnecessary sequential `Q` then `Qh` on this root | Rejected for the extracted production map: `Q` begins at complexes, `Qh` at K, and `toD'` reuses `Qh`; the observed K argument enters one lift. | **[API/source evidence; Direct child replay]** |
| H2: equivalent names expose different target representations | `Q` and `Qh` have different domains and are connected after the homotopy quotient by a natural iso. No valid same-K-pair alternate `Q.map` representation exists. | **[API/source evidence]** |
| H3: D/D' spelling changes target Hom instance | The alias exposure and category-instance checks are immediate; the original sides select the same `instCategoryDerivedMonoidal` declaration with different arguments. No independent MC-D versus MC-D' alignment control was obtained. | **[Direct child replay; API/source evidence; Unknown]** |
| H4: source mismatch is already expensive | Supported by the exact outer K pair's 12.914 s and persistent `quasiIso`/monoidal-provider divergence. | **[Direct child replay]** |
| H5: quotient lifting materially amplifies the mismatch | Not supported as a dominant factor: same-pair target adds about 0.854 s, while the K pair is already 12.914 s. A separate causal cost for every quotient/shrink descendant is unknown. | **[Direct child replay; Inference; Unknown]** |
| H6: target Hom/object dependency adds secondary cost | Supported by the 1.143 s shared-morphism residual and endpoint/type controls. | **[Counterfactual]** |
| H7: `map_comp` compares two RHS transports | Supported: two distinct RHS map Exprs and two disjoint expensive RHS descendants; exact per-map quotient/shrink reduction attribution remains unresolved. | **[Direct root evidence; Direct child replay; Unknown]** |

No repeated `Shrink`/`equivShrink` wrapping beyond the expected selected target representation was found in the extracted map output. A full recursive occurrence/DAG census of the entire original Expr was not captured, so this is a statement about the inspected production path, not a global absence proof. **[Direct child replay; API/source evidence; Unknown]**

## 7. Decision, questions, and limits (P7)

**Outcome E is best supported:** the exact source pair is already expensive; `Qh`/`toD'` is the expected single K-to-D path; target Hom/object dependence adds a bounded secondary residual; and `map_comp` pays for two distinct RHS maps. No Q/Qh misuse is supported by the inspected types, values, or Expr path. **[Direct root evidence; Direct child replay; API/source evidence; Counterfactual; Inference]**

Questions 1-4: the exact declarations are in section 1; `Q` and `Qh` have different domains with a quotient-composition natural iso; the extracted production map enters one `Qh` lift and the expected quotient/shrink target representation. Whole-root dynamic reduction counts are in section 2 and are not syntactic transport counts. **[API/source evidence; Direct child replay; Direct root evidence]**

Questions 5-7: exact outer K source/output comparisons are 12.914/13.768 s exclusive in direct child replays; inner K/output checks are about 0.67 s; sharing morphisms leaves 1.143 s wall, while sharing endpoints removes the selected Hom-type comparison. Raw `Q0`/`Q` checks on the K pair are ill-typed. **[Direct child replay; Counterfactual; API/source evidence]**

Questions 8-9: two distinct RHS map descendants account for 8.768 and 13.632 s in the direct `map_comp` replay. D/D' is a type alias; the inspected selected category declaration is the same on both sides, but an independently aligned MC-D versus MC-D' provider control is unknown. **[Direct child replay; API/source evidence; Unknown]**

Questions 10-12: the Q/Qh misuse hypothesis is rejected for the inspected map path; source and repeated RHS work dominate the measured tree, with an endpoint-dependent residual. The table in section 2 is same-root non-overlapping attribution; stage timings and shared-argument interventions are replays and counterfactuals. A finer same-root semantic-layer split and complete call-ID/Expr-DAG census are unknown, so no numerical claim is made for an independent quotient/shrink multiplier. **[Direct root evidence; Direct child replay; Counterfactual; Inference; Unknown]**
