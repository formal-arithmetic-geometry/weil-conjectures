# Slow Derived Tensor: Morphism and DerivedMonoidal Cost Report

## 10.1 Baseline and exact compared terms

This round used fresh measurements on pinned Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11cda51a86af692955474`, consumer `bdab171985a`, and the observational READY4.2 kernel. The exact historical root was the Kernel comparison of the inferred and declared types of `icd_tensorObj_probe`, with its original twelve-binder local context. Every Lean invocation had a 3600 s timeout; no more than two investigation jobs ran together. No Kernel decision rule, theorem source, commit, or push was changed. The later-consumer exploratory trace was excluded from every result below. [Direct root evidence]

Write `C = HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up Int)`, `D = DerivedCategory (Sheaf X.smallEtaleTopology A)`, `Qh = DerivedCategory.Qh`, and `H = DerivedMonoidal Qh (HomotopyCategory.quasiIso ...)`. The exact source expressions are `F_L = curriedTensor C` composed with `(Functor.whiskeringRight C C H).obj (toDerivedMonoidal Qh quasiIso_L)` and the corresponding `F_R` with `quasiIso_R`. The compared generated functors are `U_L = Functor.uncurry.obj F_L` and `U_R = Functor.uncurry.obj F_R`, of type `Functor (C × C) H`. The left `curriedTensor` instance is `HomotopyCategory.MonoidalCategory.instMonoidalCategory`; the right is the global `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures`. Exact Expr heads, hashes, and types are in `map-probe.txt` and `comp-probe.txt`; their printed source syntax is identical despite unequal elaborated Exprs. [Direct child replay]

| Fresh same-root subtree | Calls | Exclusive time |
|---|---:|---:|
| Root | 6,239,533 | 63.617 s |
| `U.obj` | 56,018 | 0.721 s |
| `U.map` | 1,902,386 | 18.956 s |
| `U.map_id` | 84,173 | 0.846 s |
| `U.map_comp` | 4,196,856 | 43.090 s |

These are disjoint field subtrees of one root. The earlier 72.354 s root, 21.412 s `map`, and 48.869 s `map_comp` are historical baseline measurements in a different run; no time from that run is added to this table. Root call IDs 1 -> 2 -> 6 -> 7 -> 8 -> 9 -> 10 -> 11 -> 40 -> 41 expose the dependent proposition and generated `Functor.mk`; `map` is call 56065, parent 41, and its instantiated composition body is call 56066. The bounded raw-event capture ends during `map`, so `map_comp`'s same-root lineage is identified by the root path summary and separate exact endpoint replays, not a claimed raw call ID. [Direct root evidence]

## 10.2 `uncurry.map` attribution (A, P1/P4)

The instantiated body has head `CategoryStruct.comp/7` and is `(F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2`. Its target is a `Quiver.Hom` in `H`; the target category argument is `instCategoryDerivedMonoidal` projected to `CategoryStruct`. The first factor has head `NatTrans.app/8`, contains the outer `F.map` and `curriedTensor.map`/`whiskerRight`, and the second has head `Functor.map/8`, containing `curriedTensor.obj`/`whiskerLeft`. The source-instance providers survive below both and in `tensorObj`-dependent target objects. [Direct child replay; Direct API expansion]

| Component | Fresh same-root observation | Independent replay, separate cache/context |
|---|---|---|
| Full map body / target composition | 1,902,386 calls; 18.956 s | 1,902,432 calls; 20.007 s trace, 13.390 s counters |
| Outer `NatTrans.app` factor | Root map descends through a 17.391 s localization/composition argument subtree; this includes descendants and is not the app head cost | 1,846,115 calls; 13.492 s counters; 19.940 s trace |
| Inner `Functor.map` factor | Within the remaining map subtree; no disjoint same-root total exported | 112,288 calls; 0.673 s counters; 1.849 s trace |
| Target Hom/domain/codomain | Dependent types occur in the composition arguments; disjoint root map total not exported | 112,002 calls; 0.657 s counters for the full result Hom pair |
| Target composition head | One original root `CategoryStruct.comp` delta aggregate: 201,311 unfolds / 0.017 s across *all* fields | With morphism arguments shared: 1.056 s / 168,003 calls; with all object and morphism arguments shared: below 1 ms wall resolution, both Kernel-valid |
| `NatTrans.app` head | 542,714 root delta unfolds / 0.059 s across all fields | The large factor replay includes its outer-map descendants |

The root's outer 17.391 s path is nested below the target composition and localization category projection. Charging that inclusive path again to the composition head would double count. The exact first unequal structural leaf in the printed pair is the universe-instantiated `quasiIso`; the first operational source branch is `Functor.comp` argument 6, `curriedTensor`'s monoidal instance. The expensive outer route reaches `whiskerRight` through `F.map`, while `NatTrans.app` exposes that natural-transformation component. The inner `whiskerLeft` route is independently much smaller. These child replay times are diagnostic, not a partition of 18.956 s. [Direct root evidence; Direct child replay; Inference for operational route]

## 10.3 `uncurry.map_comp` attribution (B, P2)

Proof irrelevance enters `Functor.uncurry._proof_3`: the proof body is skipped and its dependent proposition type is compared. Its five instantiated domains are three pointer-shared `Prod` object domains and two pointer-shared `Quiver.Hom` morphism domains. All compare equal. A separate trace replay spent 2.900 s setting up domain 0 and 0 ms on the remaining four; those setup costs are not added to the root. The conclusion is `Eq (Quiver.Hom ...) lhs rhs`. [Direct root evidence; Direct child replay]

| Same-root, non-overlapping conclusion child | Calls represented by independent replay | Fresh root exclusive |
|---|---:|---:|
| Target Hom equality carrier, `Eq.arg0` | 112,002 | 1.138 s |
| LHS, `Eq.arg1` = `uncurry.map (f ≫ g)` | 1,902,432 | 19.027 s |
| RHS, `Eq.arg2` = `uncurry.map f ≫ uncurry.map g` | 3,301,411 | 22.925 s |
| `map_comp` total | 4,196,856 | 43.090 s |

The LHS has one target `CategoryStruct.comp/7` with a composite product morphism. Its argument 5 is one `NatTrans.app/8` outer map (26.663 s counters replay), and argument 6 is one inner `Functor.map/8` (1.868 s counters replay). The RHS has a final target `CategoryStruct.comp/7` whose arguments 5 and 6 are **two distinct** `CategoryStruct.comp/7` uncurried maps (26.910 and 28.062 s counters replays). Each contains outer/inner source maps transported into target Hom. The independent endpoint replays took 20.007 s (LHS) and 35.728 s (RHS) in trace mode, or 27.287 s and 54.405 s in the later counters child drill; their timings overlap and are not a root partition. [Direct child replay; Direct API expansion]

The historical same-root gap was 4.447 s (26.013 minus 21.566). The **fresh** same-root gap is 3.898 s (22.925 minus 19.027), under the same instrumentation mode for both children. The structural reason is the RHS's second separately transported uncurried map and intermediate target morphism: it has two full composition arguments where the LHS has one outer natural-transformation factor and one cheap inner map. Root caching and reduction context mean the extra independent replay time cannot be subtracted to produce a 4.447 s child charge. The exact responsible RHS branch is the final composition's second uncurried-map argument together with the first; the trace does not provide a non-overlapping finer split of those arguments in the original root. Both endpoints retain the source instance mismatch. [Direct root evidence; Direct child replay; Inference for the causal explanation; Unknown for finer same-root split]

## 10.4 `DerivedMonoidal` verification (C, P3/P4)

The pinned definitions reduce as `DerivedMonoidal L W := D`, `toDerivedMonoidal L W := L`, and `Category (DerivedMonoidal L W) := inferInstanceAs (Category D)`. Fresh target-type WHNF exposed the exact `DerivedMonoidal` arguments as the underlying `Quotient` target on both sides, pointer shared after exposure. Each alias-versus-exposed DefEq check returned true in 0 ms at millisecond resolution; exposing both sides also took 0 ms. The original morphism Exprs and monoidal-instance mismatch were unchanged. This is a transparency diagnostic, not a new category. [Direct child replay; Direct API expansion]

The original root unfolded `toDerivedMonoidal` twice in **0.004 ms total delta time**, `DerivedCategory.Qh` twice in **0.006 ms**, and `Functor.map` 204,388 times in **0.021 s total delta time** across every use. The last aggregate is only an upper bound on map-head unfolding; it is not an exclusive cost for `toDerivedMonoidal.map` or for comparing its output. The target `CategoryStruct.comp` head likewise unfolded 201,311 times in 0.017 s; its large *subtrees* descend into morphism arguments and dependent target types. [Direct root evidence]

The target Hom pair for the exact map result was `Quiver.Hom/4`, with unequal target object Exprs and `instCategoryDerivedMonoidal` on both sides. Comparing it separately took 112,002 calls / 0.657 s in counters mode; the `map_comp` carrier cost 1.138 s same-root. The root Hom carrier descended into `ShrinkHoms.instCategory._proof_1`, which has a 111,951-call / 1.138 s descendant, but this is target *type* work, not the main morphism endpoint work. No fresh direct comparison of pre-transport source Hom types was isolated from these dependent objects. [Direct root evidence; Direct child replay; Unknown for isolated pre-transport split]

## 10.5 Source/target interaction (D, P6)

| Variant/diagnostic | Source mismatch | Target representation | Fresh result | Original M0? |
|---|---|---|---|---|
| D00 | Original | `DerivedMonoidal` | Root 6,239,533 calls / 63.617 s; exact `map` body 1,902,432 calls / 13.390 s counters replay | Yes for root; child is exact extracted pair |
| D10 | Aligned monoidal instance | Same | Kernel-valid `U` 3.455 ms / 370 calls; `map` 1.122 ms / 69 calls; `map_comp` 2.076 ms / 215 calls | No, API-level counterfactual |
| D01 | Original | Alias exposed as underlying target | Target-type alias checks true in 0 ms; the morphism pair was not altered | No, transparency diagnostic only |
| D11 | Aligned | Alias exposed as underlying target | Fresh aligned `U` 6 ms; both exposed target types pointer shared; alias checks true in 0 ms | No, API-level counterfactual plus transparency diagnostic |

The fixed-argument diagnostics were Kernel-checked before comparison. For the exact original `map` composition pair, sharing only morphisms left 168,003 calls / 1.056 s; sharing object arguments as well completed below 1 ms wall resolution, against 1,902,432 calls / 13.390 s with source-derived arguments in the same counters probe. These diagnostics change the measured pair, not M0. They demonstrate that the source-derived morphisms account for most comparison work, with a measurable residual when object arguments still differ. D01/D11 expose only the definitional target alias; neither builds a distinct whole-`U` target representation. A valid alternative type-preserving target category was unavailable, so an independent intrinsic target amplification factor remains unquantified. [API-level counterfactual; Direct child replay; Unknown for alternative target]

**D5 verdict:** D0 is supported for the alias (negligible wrapper reduction); D1 is directly observed (target Hom and composition are comparison sites); D3 is supported for the source-mismatch-dependent cost in the exact target composition; D2 as an independent target representation effect is unresolved. The target is not an independent mismatch producer. [Direct root evidence; API-level counterfactual; Inference for interaction]

## 10.6 Instance-field-to-cost mapping (E, P5)

| Source instance field | Exact route in `map` | LHS / RHS route in `map_comp` | Cost evidence |
|---|---|---|---|
| `tensorObj` | Target object and Hom domains under `curriedTensor.obj` | Domains of the one LHS map and both RHS maps | Root projection lineage; no disjoint morphism-only field time |
| `whiskerRight` | `curriedTensor.map` -> outer `F.map` -> `NatTrans.app`, root map's dominant path | One LHS outer factor; one in each RHS uncurried map | Fresh outer/inner child replays; prior single-field alignment collapses `U` to 4.4 s |
| `whiskerLeft` | `(F.obj Y.1).map f.2`, inner factor | One LHS inner factor; one per RHS uncurried map | Fresh inner replay 0.673 s counters; prior isolated alignment leaves expensive path |
| `tensorHom` | No direct projection observed | No direct projection observed | Unknown as a direct root cost; standalone field timing is not charged here |
| Law/coherence fields | No direct projection observed | Proof body skipped; dependent endpoint types compared | No direct monoidal-law cost charged to root |

The `whiskerRight` and `whiskerLeft` paths are exact source/API projections; their independent replay times must not be added to the same-root map or endpoint totals. The earlier field alignment is cited only as established causal context, not presented as a new measurement. [Direct root evidence; Direct child replay; Direct API expansion; Inference for field-specific route]

## 10.7 Evidence classification and decision

**Section 11 decision: Outcome C, with the limitation of E for independent target amplification.** The fresh root and exact child replays demonstrate the source difference entering target compositions, and the valid fixed-argument diagnostic drops the exact map comparison from 13.390 s to 1.056 s or below 1 ms with all arguments shared. Source-instance alignment also removes the generated-field path. This establishes a source/target *comparison interaction*, not an intrinsically slow `DerivedMonoidal` wrapper or a quantified alternative-target penalty. Outcome D is contradicted by measured alias/map-head reductions. Outcome B's independent target-representation claim is not established without a valid alternative category. [Direct root evidence; Direct child replay; API-level counterfactual; Inference for decision; Unknown for intrinsic target share]

The root/field/endpoints and delta totals are direct root evidence. The exact map, endpoint, Hom, and shared-argument checks are direct child replays. Source alignment and fixed arguments are API-level counterfactuals and do not preserve M0. The explanation that the extra RHS map causes the gap is an inference from measured child structure and same-root endpoint totals; a numerical non-overlapping split of the second RHS map is unknown. [Evidence classification]

## 10.8 Remaining questions and answers to section 12

The exact source/target expressions for `map` are in 10.2; the binder domains and exact endpoint heads and children for `map_comp` are in 10.3. The fresh root's target Hom carrier takes 1.138 s, versus 19.027/22.925 s in morphism endpoints. The wrapper's own delta is 0.004 ms, and target composition-head delta is 0.017 s *across the root*, whereas its argument descendants dominate. Exposing the alias changed no measurable reduction at millisecond resolution. The target is a measured comparison context whose cost depends on the source mismatch, but its independent representation share is unknown. The two remaining technical questions are a valid type-preserving alternative target representation and a bounded same-root event capture of the complete `map_comp` argument subtree with call IDs. No unverified field or proof-law cost is attributed here.

Reduced source probes, root path summaries, selected call-ID events, and sanitized compiler excerpts are in `sdtmdc/`. Every reduced file is below 5 MB. The raw traces remained in Weil scratch and none exceeded 2 GB. Weil disk usage was 85% at the final check. No commit or push was made.
