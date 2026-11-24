# Slow Derived Tensor: Uncurrying Amplification and `map_comp` Cost Report

## Scope and evidence labels

Pinned environment: Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, consumer `bdab171985a`, with READY4.2 observational instrumentation. The fresh original-root replay (`R=1190`) returned `true`, used 6,239,530 recursive DefEq calls, 47.686 s comparison-exclusive time, 24.090 s reduction-exclusive time, and 71.775 s observer-heavy time. This wall time is used only for same-run shares.

Evidence labels: **direct root evidence** means the fresh `tensorObj` root; **direct child replay** means a separately invoked comparison of an exact extracted child; **counterfactual** means a rebuilt expression/control that changes the original obligation. Every control below is an **API-level counterfactual** unless explicitly stated otherwise. No M0-preserving cut was established. No original-root trace entered a selected right Kan extension or counit body.

## 14.1 Source representation

The source terms have this printed form (the exact elaborated Exprs are retained in the probe output):

```lean
F_L = curriedTensor (HomotopyCategory ... ) ⋙
  (Functor.whiskeringRight ... (DerivedMonoidal ...)).obj
    (toDerivedMonoidal DerivedCategory.Qh (HomotopyCategory.quasiIso ...))
F_R = curriedTensor (HomotopyCategory ... ) ⋙
  (Functor.whiskeringRight ... (DerivedMonoidal ...)).obj
    (toDerivedMonoidal DerivedCategory.Qh (HomotopyCategory.quasiIso ...))
```

Here `C` is `HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)` and `H` is `DerivedMonoidal DerivedCategory.Qh (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))`. Both source types have the form `C ⥤ C ⥤ H`; their exact elaborated types, instance arguments, hashes, and selected Expr paths are retained in `uae-probe.out`. **Evidence: Demonstrated, direct child replay.**

They have the same printed form but different Exprs (fresh sizes 63,691/52,459; hashes differ). The first exact structural leaf exposed by the source probe is the universe-instantiated `HomotopyCategory.quasiIso`: `max (succ u) u'` on the left versus `max (max u' (succ u)) u` on the right. The first operational branch in the direct source tree is `Functor.comp` argument 6, `curriedTensor`: its monoidal instance is `HomotopyCategory.MonoidalCategory.instMonoidalCategory` on the left and the named `the named historical monoidal instance` on the right. The source target/category arguments and the `toDerivedMonoidal` wrapper are also pointer-unequal; the source product/category arguments of `uncurry` are shared. **Evidence: Demonstrated, direct child replay.**

Direct `F_L ≟ F_R`: 28,223 calls, 0.234 s in the fresh probe (**direct child replay**; prior same setup was about 0.998 s). The tree terminates at the `Functor.comp`/`curriedTensor` representation after reducing instance/proof arguments; it does not enter the generated uncurried fields. The fresh root reaches the source through the existence proposition and then exposes `uncurry` (**direct root evidence**).

## 14.2 Uncurrying amplification

The pinned implementation is:

```lean
obj F := { obj := fun X => (F.obj X.1).obj X.2
           map := fun {X} {Y} f => (F.map f.1).app X.2 ≫ (F.obj Y.1).map f.2
           map_comp := by
             simp only [prod_comp_fst, prod_comp_snd, Functor.map_comp,
               NatTrans.comp_app, Category.assoc]
             slice_lhs 2 3 => rw [← NatTrans.naturality]
             rw [Category.assoc] }
```

The expensive constructor is `Functor.mk` produced by reducing `uncurry.obj F` (root call 38, parent 37), with result type `Functor (C × C) (DerivedMonoidal ...)`. Constructor arguments 0--3 are parameters; arguments 4--7 are exactly `obj`, `map`, `map_id`, `map_comp`. Fresh selected metadata records these field types: `map` 170,335/148,003 nodes; `map_id` 817,165/705,477; `map_comp` 2,105,085/1,814,673 (`sizeWithoutSharing`). All four field expressions are pointer-unequal. **Evidence: Demonstrated, direct root evidence.**

`uncurry` therefore does more than repackage `F`: it creates a data-valued map containing outer mapping, a natural-transformation component, inner mapping, and target composition, and it creates dependent proof fields whose proposition types repeat those operations. The direct source comparison never visits these generated fields. **Evidence: Demonstrated, direct root plus child replay.**

## 14.3 `map_comp` decomposition

Fresh same-root field totals are below. Round 3's heavier observer measured the same calls with 155.555 s in `map_comp` and 80.589 s in `map`; absolute times from those different observer modes are not pooled.

| Component | Calls | Exclusive time | Evidence |
|---|---:|---:|---|
| `map_comp` field total | 4,196,856 | 48.869 s | direct root evidence |
| dependent binder domains | 5 extracted domains; domains 0--4 compare as equal | domain 0 2.937 s; remaining domains 0 s in direct replay | direct child replay |
| equality type (`Eq.arg0`, target Hom) | 112,002 calls in replay | 1.290 s same-root subtree; 3.324 s endpoint replay | direct root and child replay |
| equality LHS (`Eq.arg1`) | not independently counted in root summary | 21.566 s same-root subtree; 22.563 s endpoint replay | direct root and child replay |
| equality RHS (`Eq.arg2`) | not independently counted in root summary | 26.013 s same-root subtree; 41.415 s endpoint replay | direct root and child replay |
| exact equality conclusion | 4,196,946 calls | 53.074 s inclusive replay | direct child replay |

The instantiated telescope is five binders: three product objects followed by two product morphisms. Their displayed domains are pointer-identical (`Prod`, `Prod`, `Prod`, `Quiver.Hom`, `Quiver.Hom`); only the first domain incurs substantial setup work in separate replay. The conclusion is `Eq` over a target `Quiver.Hom`. Its LHS and RHS are `CategoryStruct.comp` terms. The same-root `Eq` argument subtrees partition the 48.869 s field time to rounding: RHS 26.013 s, LHS 21.566 s, carrier 1.290 s. The separate endpoint replays overlap and must not be summed. **Evidence: Demonstrated for the same-root partition and fresh child replays.**

Proof irrelevance is entered for `uncurry.map_comp`; proof bodies are not compared. The cost is the dependent proposition type, especially the equality endpoints, not the witness body. The fresh branch distribution includes 78,836 proof-irrelevance entries, 1,258,739 application branches, 1,099,014 projection branches, 308,993 second-WHNF branches, and 3,348,127 quick branches. These are direct root evidence; branch labels are observational strategy labels, not semantic claims.

## 14.4 `map` decomposition

Fresh root `map` field: 1,902,386 calls and 21.412 s same-run exclusive time (29.8% of this fresh root's 71.775 s). The exact map body is `CategoryStruct.comp/7` with seven arguments. Direct child replay results:

| Component | Calls | Replay time | Evidence |
|---|---:|---:|---|
| outer map / `NatTrans.app` argument | 1,846,115 | 20.002 s | direct child replay |
| `NatTrans.app` local comparison | 1,846,115 argument path; 21.261 s | direct child replay |
| inner `Functor.map` argument | 112,288 | 0.983 s | direct child replay |
| target `CategoryStruct.comp` body | 1,902,432 | 21.202 s | direct child replay |
| `NatTrans.app` delta itself | 542,714 unfolds, 0.366 s delta in the fresh run (0.561 s in round 3) | direct root evidence |

A one-level map replay shows the `NatTrans.app` application has eight arguments. Its expensive argument is the outer `Functor.map/8` (34.676 s child replay); the two nested outer `Functor.obj` arguments are about 3.9--4.2 s each. The inner map child is much smaller. Thus `NatTrans.app` is a structural gateway; its own delta reduction is not the cause. **Evidence: Strongly supported, direct child replay plus direct root.**

## 14.5 Cheap-field controls

`obj` is 56,018 calls / 0.530 s in the fresh root; `map_id` is 84,173 calls / 0.962 s. `obj` only compares object actions and does not build a target morphism composition. `map_id` is proof-irrelevant, but its dependent identity proposition has one identity-shaped endpoint and fewer nested compositions than `map_comp`. Both still carry the same hidden target/provider difference, but expose less morphism-level structure. **Evidence: Demonstrated for cost and proof irrelevance; causal explanation Strongly supported.**

## 14.6 Source/provider controls

| Control | Changed factor | Result | Label |
|---|---|---|---|
| Original | none | `F`: 28,223 calls; `U`: 6,239,463 calls in fresh direct child replays | M0 pair, direct child replay |
| G1 | target type argument only (`Functor.comp` argument 4) | `uncurry` remains 6,239,463 calls / 71.242 s | API-level counterfactual, Demonstrated |
| G2 | quasi-isomorphism/universe provider only | not independently measured as a valid same-typed replacement | API-level counterfactual, Unknown |
| G3 | `curriedTensor` factor wholesale (`Functor.comp` argument 6) | `F` 2 ms; `uncurry` 6 ms | API-level counterfactual, Demonstrated |
| G4 | monoidal instance argument only (argument 2 of `curriedTensor`) | `F` 2 ms; `uncurry` 5 ms; fields: `obj` 0 ms, `map` 2 ms, `map_id` 2 ms, `map_comp` 3 ms | API-level counterfactual, Demonstrated |
| G5 | target category instance only (`Functor.comp` argument 5) | `uncurry` remains 6,239,463 calls / 72.449 s | API-level counterfactual, Demonstrated |
| G6 | whiskering/source wrapper only (`Functor.comp` argument 7) | `uncurry` remains 6,239,463 calls / 78.110 s | API-level counterfactual, Demonstrated |

G4 is the dominant source/provider control. It aligns the exact hidden monoidal instance while leaving the source wrapper and target provider otherwise rebuilt. G1, G5, and G6 retain the expensive path. No control preserved the original M0 theorem obligation; none is evidence that the theorem itself can be changed without changing its API-level terms.

## 14.7 Causal conclusion

**Both `map` and `map_comp` materially amplify the source representation mismatch, with `map_comp` dominant through its dependent equality endpoints.** The hidden mismatch first appears as the inferred versus named monoidal instance in `curriedTensor` (with the universe-instantiated `quasiIso` as the earliest structural leaf). `Functor.uncurry` expands that small mismatch into each generated field. `map` repeats it through outer `Functor.map`, `NatTrans.app`, inner map, and target composition. `map_comp` repeats the same map/composition structure inside a dependent proposition type; proof irrelevance skips proof bodies, but the binder/equality type still has to be compared. The fresh root shows 68.1% of time in `map_comp` and 29.8% in `map`; round 3's heavier observer reported 64.0% and 33.1%. `map_id` and `obj` are minor. The selected right Kan extension and counit are not causal observations: no original-root trace entered them.

## Answers to §15

1. First exact leaf: universe-instantiated `HomotopyCategory.quasiIso`; first operational branch: inferred versus named `curriedTensor` monoidal instance.
2. Direct `F` stops at composition/instance comparison; `uncurry` constructs and compares four generated fields and their dependent types.
3. `Functor.mk` for `Functor (C × C) (DerivedMonoidal ...)`, arguments 4 `obj`, 5 `map`, 6 `map_id`, 7 `map_comp`.
4. `map_comp` embeds the uncurried map and target composition in a dependent equality proposition; 4.197M calls and 48.869 s fresh root.
5. Equality endpoints dominate: the same-root LHS/RHS subtrees take 21.566/26.013 s, versus 1.290 s for the carrier; domains are shared, though domain 0 costs 2.937 s in a separate replay.
6. `CategoryStruct.comp` and its `NatTrans.app`/outer map child dominate; inner map is smaller.
7. Through the outer map argument and its `NatTrans.app`, with target composition carrying the resulting Hom type; not through `NatTrans.app` delta alone.
8. `obj` has no morphism composition; `map_id` has a smaller identity proposition than the two-map composition proposition.
9. Repeated branches are quick, projection, application, second-WHNF, lazy-delta, and proof-irrelevance; direct root counts are recorded above.
10. G4, aligning only `curriedTensor`’s monoidal instance, removes the dominant work; G1, G5, and G6 do not.
11. Root field totals, root branch/path data, and proof-irrelevance entry are direct root evidence. Exact map/map_comp component timings and source diff are direct child replays. G controls and direct `F`/`U` diagnostics are API-level counterfactuals/direct child replays. Right-Kan/counit claims are Not observed on the root.
12. Yes at the representation level: inferred versus named monoidal instance, with universe-instantiated provider terms, is amplified through `uncurry.map`, `map_id`, and especially the dependent `map_comp` equality endpoints. The exact same-root partition is in `root-paths.txt`; finer provider lineage through every reduction remains Unknown.

## Reproducibility and limits

Fresh probe sources remain in scratch; compact outputs and root summaries are in `sdtuae/`, all below 5 MB. Raw traces were not copied to the repository. The instrumentation only observes kernel comparisons and does not alter kernel decisions. At most three Lean jobs were used; disk usage was checked at 85%. M1/M2 provenance labels are not used as causal evidence. The monoidal-instance G4 control changes the compared source expression and is therefore an API-level counterfactual, not an M0-preserving local cut.
