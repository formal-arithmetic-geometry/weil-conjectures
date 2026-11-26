# Slow Derived Tensor: shortcut unfolding and provider causality (round 9b)

## Evidence and scope

`[O]` means direct original-root evidence from the pinned READY4.2 trace; `[R]` a fresh twelve-binder exact-source replay; `[C]` a direct extracted-child replay; `[A]` a pinned declaration or implementation audit; `[K]` a type-correct API counterfactual; `[I]` an inference from cited observations; `[U]` an unmeasured or unresolved link. Replay Expr hashes contain local free-variable identities and are comparable only within one run. The saved historical root is a path trace, not a serialized Expr. No number from an earlier round is presented as a new result. [O,R,A,U]

The fresh runs used Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11cda51a86af692955474`, consumer `bdab171985a5e6c6e44fc3920386b89fc5627ca3`, and the observational READY4.2 Kernel. They used isolated scratch copies, at most three investigation Lean processes, and a 3600 s timeout per invocation. The final disk reading was 82%. A 3.4 GB raw trace was deleted; the retained compressed trace is scratch only. [R,A]

## 1. Established shortcut-to-canonical relationship

The shortcut's compiled value applies `HomotopyCategory.MonoidalCategory.instMonoidalCategory` to 19 arguments. Its final source `inferInstance` selects that canonical declaration before the shortcut itself is registered. Delta unfolding can therefore expose canonical without another synthesis event. The shortcut's canonical application includes generated `_proof_3` through `_proof_12` arguments, so this is a wrapper around the canonical construction, not a second independent instance. [A; verified against the fresh declaration/reduction replay]

## 2. Shortcut applications before reduction

The fresh twelve-binder extraction finds a direct shortcut constant on both checked and stored sides of the unreduced final `Eq`; the level vector is `[u + 1, max (u + 1) u']` on both sides. The checked and stored parents are different provider spines: checked `inferInstance` targets `MonoidalCategoryStruct (DerivedCategory ...)`, while stored `inferInstance` targets `MonoidalCategoryStruct (DerivedMonoidal ...)`. Their instance arguments are respectively `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory` and `DerivedMonoidal.instMonoidalCategory`; these are definitionally related but structurally unequal. [R]

| Component | Checked | Stored | Status |
| --- | --- | --- | --- |
| Shortcut head | `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures` | same | Equal [R] |
| Levels | `[u + 1, max (u + 1) u']` | same | Equal [R] |
| Source category | `Sheaf X.smallEtaleTopology A` | same printed category | Direct argument equality not completed [R,U] |
| Eight ordinary arguments | application occurs in the checked root | application occurs in the stored root | Per-argument pairwise equality and direct application DefEq not completed [R,U] |
| Graded tensor witness | inside the shortcut body, supplied by its final application to canonical | same compiled declaration body | No separate pre-reduction witness argument; its instantiated identity was not compared [A,U] |
| `_proof_2` | inside the shortcut body's construction | inside the same declaration body | Not one of the shortcut's eight application arguments [A] |
| Result type | `MonoidalCategory (HomotopyCategory (Sheaf ...) (.up Int))` | same target shape | Exact type hash pair not captured [R,U] |
| Parent | derived-category provider | derived-monoidal provider | Unequal spines [R] |

One additional Stage B probe reached a root with checked shortcut count zero and stored count one; it had already reduced the checked presentation. That probe cannot serve as the required unreduced pairwise comparison. Universe normalization, shared-argument substitution, swapping, and a same-shortcut parent replacement were not completed as type-correct controls. No application-argument or universe cause is established. [R,U]

## 3. Delta event and parent Kernel branch

The fresh original-style root replay succeeded with 6,267,703 DefEq calls in 74.854 s of trace wall time. It recorded 50.060 s comparison-exclusive and 24.794 s reduction-exclusive; these are same-root partitions. Across that root, the shortcut declaration had two delta calls totaling 0.021 ms. This total is the trigger's aggregate delta work, not the cost of comparing its descendants. [R]

At replay root 560, call 199 (parent 25) compares the two `MonoidalCategory.curriedTensor` applications through a `lazy_delta` argument branch. Its child call 200 compares canonical on the left with shortcut on the right (hashes `2112063830` / `281890699`, depth 10, `category=2`); call 200 descends to call 201 (`_proof_12`), and the later call 211 (parent 209) compares direct `instIsRightCancelAddOfAddRightReflectLE` with shortcut `_proof_2`, returning DefEq true. This is the first captured *canonical-versus-shortcut* comparison, not proof that call 200 is the earlier checked-side shortcut delta event. [R]

The event recorder's `initial_whnf` row at call 200 reports unchanged heads and `reduced_side=none`; it does not serialize the shortcut-before/canonical-after step or its precise WHNF caller. The checked-side transition occurred before this child pair was entered, during provider exposure. Thus the plan's requested exact first delta event, its parent call ID, and its value-versus-type classification remain unobserved. Root 553 call 7 separately compares shortcut with shortcut while Kernel checks the declaration; conflating that call with root 560 would be incorrect. [R,U]

## 4. Why checked and stored reduce differently

Fresh direct WHNF of the checked and stored provider expressions, in one replay environment and local context, yields `MonoidalCategoryStruct.mk/10` on both sides. The resulting structures have different hashes and sizes: checked `686654666`, size 1,753,267; stored `3781244708`, size 1,103,755. Fresh path extraction finds canonical applications in the checked reduced graph and shortcut applications in the stored reduced graph, repeating the round-8 asymmetry. Both cross-direction provider DefEq calls returned true in the focused probe. [R,C]

The operands of direct WHNF differ before reduction: checked provider type contains a more nested universe `max` expression and goes through `DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory`; stored provider goes through `DerivedMonoidal.instMonoidalCategory`. The data therefore support an earlier reduction-path/context difference, but do not isolate which step caused the nested checked shortcut to unfold. The focused G5 full-root control timed out at the meta `whnf` heartbeat limit before completing; no historical-root-only asymmetry claim is made. [R,C,I,U]

## 5. Projection and dependent-type context

The fresh root field replay descends from `Eq` argument 2 through provider WHNF to `MonoidalCategoryStruct.mk`; its `tensorObj` fields are unequal Exprs (sizes 61,073/38,661) with the same printed lambda and Kernel DefEq true in 72.652 s. Thus WHNF of the surrounding provider is demanded before the expensive `tensorObj` field comparison. [R,C]

The root path then enters `RightExtension.obj`, a `Functor.mk`, and `Functor.uncurry._proof_3`'s **proposition type**: the `Eq` there has a 48.163 s inclusive subtree in this fresh trace. The `map_comp` endpoints below its proposition type contain target `CategoryStruct.comp`; the separate map body follows `NatTrans.app` and `Functor.map`. The original trace does not attach the first shortcut delta event to one projection, generic-field dependent type, or `whiskerRight` caller ID. It establishes a dependent proposition comparison as the expensive downstream context, not as the proven initial delta trigger. [R,I,U]

| Context | Shortcut / reduction observation | Expensive descendants |
| --- | --- | --- |
| `tensorObj` provider | Shortcut before provider WHNF; checked canonical and stored shortcut in reduced graph [R] | Field DefEq 72.652 s child replay [C] |
| Generic field argument | Nested supplied monoidal argument in derived provider; projection exposure measured [R] | Dependent `HasLeftDerivedFunctor₂` type [R] |
| `whiskerRight` | Structural source field difference and direct DefEq true [C] | `NatTrans.app` route [R,I] |
| `uncurry.map` | No new shortcut event isolated [U] | `NatTrans.app`, target composition [R] |
| `map_comp` LHS/RHS | No new shortcut event isolated [U] | Eq endpoints, target compositions [R] |

## 6. Reducibility and lazy delta

Fresh declaration metadata gives canonical `def regular(24)`, shortcut `def regular(25)`, derived wrapper `regular(27)`, `tensorObj` and `whiskerRight` projections `abbrev`. Fresh options have `lazyProjDelta`, `lazyWhnfCore`, `respectTransparency`, and `implicitBump` enabled. In pinned `ExprDefEq.lean`, `whnfCoreAtDefEq` can use projection mode `yesWithDeltaI`; `isDefEqProjDelta` invokes `isDefEqDeltaStep`, where unequal regular hints select a side only when *both current heads are delta candidates*. The actual call-200 heads are canonical/shortcut, with different hints, but the captured event omits the step's selected side. [A,R,U]

A disposable regular-height control showed `regular(1)` unfolding at `reducible`, while `regular(2)` and `(3)` remained at `reducible`/`instances` and unfolded at `default`/`all`. The source classifies height greater than two as nontrivial. These facts establish that hints can affect a lazy-delta choice; they do not establish that 24 versus 25 caused the checked/stored asymmetry. [A,K,U]

## 7. `_proof_2` origin and exact provider pair

The shortcut's internal `IsRightCancelAdd Int` synthesis selects `instIsRightCancelAddOfAddRightReflectLE`; proof extraction stores it as opaque `instMonoidalCategoryHomotopyCategoryIntUp_weilConjectures._proof_2`. In the expanded canonical-versus-shortcut fields, the first provider pair is direct `instIsRightCancelAddOfAddRightReflectLE` versus `_proof_2`, both at proposition `IsRightCancelAdd Int`. Root 560 call 211 compares this pair in a proof position, returns true, and spends 0.009 ms exclusive with 0.00044 ms reduction. Proof irrelevance explains that direct comparison's cheapness; it does not establish that the term's representation cannot affect dependent expressions elsewhere. [A,R,I]

## 8. Same-provider intervention

A fresh API-level P2 control found the exact eight-argument shortcut application inside the reduced stored `MonoidalCategoryStruct`, delta-expanded it, and replaced every exposed `_proof_2` constant in that application body with the checked side's direct four-argument `instIsRightCancelAddOfAddRightReflectLE` proof. The rebuilt structure and rebuilt stored root both passed `checkWithKernel`; the direct proof inferred type `IsRightCancelAdd Int`. An exposed-only control used the same delta-expanded body while retaining `_proof_2`, so proof replacement was the sole difference between these two constructed bodies. [K]

The P2 `whiskerRight` remains structurally unequal to P0 (sizes 169,729/117,581); the exposed-only variant also remains unequal (169,729/115,457). Both are DefEq true. P2's `tensorObj` and `whiskerLeft` fields likewise remain unequal to P0. This rules out `_proof_2` as the *sole* source of field representation divergence, but does not identify the other responsible argument or establish its share of cost. The reverse P3 construction was not run. [K,U]

| Variant | Provider | `whiskerRight` | `map` / `map_comp` / root |
| --- | --- | --- | --- |
| P0 original checked | direct provider [R] | unequal to P1 and P2, DefEq true [K] | fresh expensive exact-root trace in §3 [R] |
| P1 original stored | opaque `_proof_2` [R] | size 102,527 in P2 control [K] | extracted-local-context root comparison below 1 ms [K] |
| Exposed-only | shortcut body expanded, `_proof_2` retained [K] | size 115,457; unequal to P0 [K] | extracted-local-context root comparison below 1 ms [K] |
| P2 expanded with canonical provider | direct proof in expanded dependent bundle; Kernel valid [K] | size 117,581; unequal to P0 [K] | extracted-local-context root comparison below 1 ms [K] |
| P3 reverse provider | not constructed [U] | unknown [U] | unknown [U] |

The three extracted-local-context root comparisons all completed below the 1 ms timer resolution, including P0/P1. They therefore do not reproduce the 74.854 s original-style root and cannot distinguish provider-specific cost. `map` and `map_comp` were not measured in P2. Historical whole-`whiskerRight` alignment remains baseline context only. [K,R,U]

## 9. Link to `whiskerRight`

The extracted direct `whiskerRight` fields are structurally unequal, with first printed Expr difference `root/domain/arg/fn/arg`; their Kernel DefEq succeeds. The source functor route is `curriedTensor.map` to `Functor.whiskerRight`, then `NatTrans.app` in the outer factor of `uncurry.map`. The root trace contains this path below the `tensorObj`/derived-provider descent. The missing first-delta event ID prevents a complete parent-child ID chain from shortcut to `whiskerRight`. [C,R,I,U]

## 10. `uncurry.map` and `map_comp` costs

In the fresh root 560 trace, `Functor.uncurry._proof_3`'s proposition type carries a 48.163 s inclusive subtree; its `map_comp` Eq RHS `CategoryStruct.comp` branch carries 27.325 s and LHS 19.480 s inclusive. A separate map route through `NatTrans.app` has a 24.732 s inclusive subtree. These paths overlap the root and cannot be summed. The two shortcut delta calls take 0.021 ms in aggregate, versus 24.794 s total reduction-exclusive and 50.060 s comparison-exclusive at the root; most time is downstream comparison, but an exclusive `whiskerRight`/`map`/`map_comp` partition for this run was not captured. [R,U]

## 11. Evidence classification and limitations

The new exact-source replay measures a 74.854 s, 6,267,703-call DefEq root and its call 199→200→201/211 branch; the field and direct-provider comparisons are separate child replays. The reducibility audit is pinned implementation evidence, and the small wrapper tests are diagnostic counterfactuals. No producer semantic rule, shared checkout, target-Hom process, or historical input was changed. Each retained reduced file is below 5 MB and contains no machine address or absolute path; no commit or push was made. [R,C,A,K]

The event schema lacks the shortcut delta's own pre/post Expr and caller ID; Stage B's pairwise application controls and Stage E's same-root cost replay/reverse provider control remain incomplete. The valid P2 control disproves proof-only structural identity but does not settle proof-specific cost causality. No unique projection/dependent-type trigger follows from the available evidence. [K,U]

## 12. Remaining unknowns and decision

**§13 Outcome H, inconclusive for the central causal question.** A context-demanded unfolding is plausible because the root demands provider WHNF and later compares canonical with shortcut in a lazy-delta branch; an earlier path asymmetry is directly visible in the provider spines. The P2 control shows that provider replacement does not make `whiskerRight` structurally identical, but its cost consequence remains unmeasured in the expensive context. Outcomes A, B, C, D, E, F, and G are not selected as full causal explanations. [R,A,K,I,U]

Answers to §14: (1) compiled shortcut contains canonical [A]; (2) first exact requesting branch unknown, nearest captured parent is call 199→200 `lazy_delta` [R,U]; (3) checked/stored have different provider spines and direct-WHNF results, but the decisive step is unknown [R,U]; (4) levels and head match, all ordinary arguments and exact result-type equality are unverified [R,U]; (5) the downstream expensive call is in a proposition type, initial delta value/type position unknown [R,U]; (6) provider WHNF precedes the field comparison, first forcing projection unknown [R,U]; (7) regular heights influence policy but their actual side choice is unobserved [A,K,U]; (8) direct-provider replacement did not make `whiskerRight` structurally equal; cost effect unknown [K,U]; (9) remaining causal arguments unknown [U]; (10) shortcut delta aggregate 0.021 ms and root downstream comparison/reduction partitions as above, finer field partition unknown [R,U]; (11) asymmetry is present in the fresh source replay, historical exact event is unavailable [R,U]; (12) direct observations and limits are classified throughout. [A,R,C,K,I,U]
