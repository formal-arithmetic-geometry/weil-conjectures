# Slow Derived Tensor: derived-category provider construction and causal alignment (round 10a)

## Evidence and environment

Labels: **[R]** fresh exact-source twelve-binder root; **[C]** fresh direct child replay; **[K]** Kernel-checked API-level counterfactual; **[A]** pinned source/elaborated declaration audit; **[I]** inference; **[U]** unresolved. Expr hashes only compare within a single replay/local context. The saved historical root is not a serialized Expr, so new local-context hashes are not compared with historical hashes. [A,R]

The pinned environment is Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11cda51a86af692955474`, consumer `bdab171985a5e6c6e44fc3920386b89fc5627ca3`. All work ran in an isolated copy under `sdt-dcp`, with 3600 s process timeouts, at most three investigation Lean processes, and 84% final disk usage. READY4.2 was observational; no Kernel rule, instance search, or production hint was changed. The shared checkout, QTC run, and heartbeat cleanup were untouched. [A,R]

## 1. Exact architecture and declaration graph (revised A, P1/P7)

Write `K = HomotopyCategory (Sheaf X.smallEtaleTopology A) (ComplexShape.up Int)`, `D = DerivedCategory (Sheaf X.smallEtaleTopology A)`, `Q = DerivedCategory.Qh : K ⥤ D`, and `D' = DerivedMonoidal Q (HomotopyCategory.quasiIso ...)`. The pinned `DerivedMonoidal L W` value is its target `D`, so `D'` and `D` are definitionally equal category expressions. The wrapper's category instance is `inferInstanceAs (Category D)`. [A]

The compiled declaration chain, including an intermediate provider omitted from the shorthand model, is:

```text
MC-D = DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  body: inferInstance (DerivedCategory.instMonoidalCategory_weilConjectures ...)
  -> DerivedCategory.instMonoidalCategory_weilConjectures
     body: MonoidalCategory.mk D Category(D) _aux_1 law-fields
     -> _aux_1
        body: MonoidalCategory.toMonoidalCategoryStruct D' Category(D') MC-D'
        -> MC-D' = CategoryTheory.DerivedMonoidal.instMonoidalCategory
           body: MonoidalCategory.ofBifunctor D' Category(D') unit bifunctor
                 associator leftUnitor rightUnitor pentagon triangle
           -> HasDerivedMonoidalCategory field and supplied MC-K argument
           -> MC-K-shortcut
              body: inferInstance (MC-K-canonical ...)
```

The direct `MC-D` body is `inferInstance/2`, with argument 1 the 11-argument intermediate D provider. The intermediate `MonoidalCategory.mk/13` has structure argument 2 `_aux_1`. The `_aux_1` value is `toMonoidalCategoryStruct/3`; argument 2 is the 10-argument `MC-D'`, while arguments 0 and 1 are `D'` and its category instance. Thus `MC-D` consumes the D' structure through a generated D-level bundle, including separately generated D-level law fields. It is not simply the same instance constant under a type alias. `Q` and `W` are explicit arguments 5 and 6 of `MC-D'`; the K monoidal category is instance argument 4; the generic `HasDerivedMonoidalCategory` proof is instance argument 9. [A]

| Declaration | Universes | Hint | Applied body / role |
| --- | --- | --- | --- |
| `MC-D` | `[w,v,u]` | regular 27 | `inferInstance/2` to intermediate D provider |
| intermediate D provider | `[w,v,u]` | regular 26 | `MonoidalCategory.mk/13`, generated bundle |
| `_aux_1` | `[u_1,u_2,u_3]` | generated definition | `toMonoidalCategoryStruct/3` of `MC-D'` |
| `MC-D'` | `[u_1,u_2,u_3,u_4]` | regular 18 | `ofBifunctor/9` |
| `D'` alias | `[u_1,u_2,u_3,u_4]` | regular 2 | returns target category |
| `MC-K-canonical` | three parameters | regular 24 | canonical K construction |
| `MC-K-shortcut` | `[v,u]` | regular 25 | `inferInstance/2` with canonical body |
| `ofBifunctor` | two parameters | regular 5 | monoidal constructor |

The full binder modes, levels, head/argument hashes, and declaration Expr dumps are in `sdtdcp/declaration-spine.txt` and the scratch declaration audit. The generic field is a structure projection, not a definition with a reducibility hint. [A]

## 2. Provider spines and first divergence (revised A/P2)

At the unreduced target-provider boundary, both sides have `inferInstance/2`, but the checked argument is `MC-D` and the stored argument is `MC-D'`; their instantiated types spell `MonoidalCategoryStruct D` and `MonoidalCategoryStruct D'`. The provider terms are structurally unequal and DefEq true. Their WHNFs are both `MonoidalCategoryStruct.mk/10`, structurally unequal, with sizes 1,753,267 (checked) and 1,103,755 (stored) in the same local context; the corresponding `tensorObj`, `whiskerLeft`, and `whiskerRight` fields are also structurally unequal and DefEq true. [C]

| Boundary | Checked | Stored | First meaningful difference |
| --- | --- | --- | --- |
| Category type | `D` | `D'` | same Expr in the extracted context; DefEq <1 ms [C] |
| Target category instance | D instance | D' wrapper instance | provider spelling [A] |
| Target monoidal provider | `MC-D` via intermediate D provider | `MC-D'` | **outer provider choice, before K argument** [A,C] |
| D bridge exposed | `MonoidalCategory.mk` plus `_aux_1` | `ofBifunctor` | generated D bundle versus direct D' construction [A] |
| D' embedded/direct | `_aux_1` argument 2 | direct `MC-D'` | same declaration role; instantiated Expr pair not fully normalized [A,U] |
| Generic field | within dependent provider | within direct D' provider | supplied K argument remains nested [A,R] |
| K before shortcut delta | `MC-K-shortcut` | `MC-K-shortcut` | equal head/levels; full ordinary argument pair unavailable [R,U] |
| K after checked reduction | `MC-K-canonical` | `MC-K-shortcut` | reduction presentation [C,R] |

The fresh original-body extraction contains one stored shortcut application and zero checked shortcut applications: checked provider exposure has already reduced that side. The stored application has eight ordinary arguments, levels `[u+1, max (u+1) u']`, and result type `MonoidalCategory K`; its application Expr and all eight arguments are exported in `sdtdcp/shortcut-app.txt`. The corresponding *unreduced checked* eight-argument application was not recovered, so per-argument pairwise equality, graded witness identity, and exact result-type equality of the two shortcut applications remain **unknown**. The directly compared canonical/shortcut applications under provider WHNF have equal inferred type hashes in one context, but that does not fill the missing unreduced pairwise comparison. [C,R,U]

## 3. Reduction lineage and lazy delta (revised B/P3)

The new exact-source root is root 557. Its first path is `Eq` call 2 -> `tensorObj` argument call 6 -> provider/projected WHNF calls 7-9 -> generic `curriedTensor_hasLeftDerivedFunctor₂` call 10 -> dependent proposition type call 11 -> `Functor.mk` call 41. The generic field's source supplies the K instance through `curriedTensor`; the checked reduced provider graph exposes canonical while the stored graph retains shortcut. The selected call-82 child compares direct `instIsRightCancelAddOfAddRightReflectLE` with shortcut `_proof_2` in a lazy-delta argument branch and returns DefEq true. [R,C]

The same fresh root records one shortcut delta (0.023 ms), two canonical deltas (0.073 ms), one `MC-D` delta (0.031 ms), one intermediate D-provider delta (0.079 ms), one `_aux_1` delta (0.133 ms), and two `MC-D'` deltas (0.034 ms). These are aggregate unfolding times, not downstream comparison charges. The bounded event recorder supplies parent-child IDs, pre/post heads and hashes, branch, selected reduced side, and first-divergence path for its captured prefix. It does **not** serialize full Expr dumps, types, universe vectors, or the original shortcut-before/canonical-after delta event with its exact WHNF caller. The first shortcut delta's selected side and the pinned lazy-delta decision at that event remain unknown; the regular 24/25 hint difference alone does not establish the decision. [R,A,U]

## 4. D-level alignment matrix (revised C/P4)

One explicit target-provider term was substituted in both directions in the twelve-binder local body. Rebuilt bodies and closed types passed `checkWithKernel`; provider WHNF and fields remained DefEq. A direct canonical K application substituted for the stored shortcut also passed `checkWithKernel`, as did the combined D/K substitution. All four local-body and reconstructed closed-type pairwise DefEq calls returned true in less than 1 ms. This indicates the extracted comparison did not reproduce the expensive root. [K]

| Cell | Intervention | Kernel check | Pairwise comparison | Causal cost result |
| --- | --- | --- | --- | --- |
| C00 | original checked/stored | original root true | 6,239,533 calls / 62.349 s same-root exclusive | fresh baseline [R] |
| C10 forward | stored provider replaced by checked `P-D` | true | DefEq true, <1 ms extracted/closed pair | unavailable for expensive-root attribution [K,U] |
| C10 reverse | checked provider replaced by stored `P-D'` | true | DefEq true, <1 ms extracted/closed pair | unavailable [K,U] |
| C01 | stored shortcut replaced by canonical K application | true in extracted local context; **false in original closed binder graph** | local DefEq true; closed comparison returned error | unavailable: bound-variable dependency [K,U] |
| C11 | both substitutions | true | DefEq true, <1 ms extracted/closed pair | unavailable [K,U] |

READY4.2 also recorded eight approximately 59-65 s / 6.24-6.27 million-call roots while `checkWithKernel` validated reconstructed closed expressions. A separate original-closed-graph probe reproduced 6,239,533-call validation roots at 44.842 s and 49.711 s for its first checked variants. They are **checking costs**, not the subsequent controlled DefEq comparison costs; their root IDs are not mapped to C10/C01/C11 as original-obligation measurements. They therefore cannot establish whether D alignment, K alignment, or both remove the original expensive path. Every intervention changes the API-level compared expression and is not an M0-preserving local cut. [K,R,U]

## 5. Fixed D-route K controls and wrapper control (revised D/§4/P5/P7)

With the same D' route on both sides, D0 keeps shortcut, D1 expands shortcut, and D2 expands it while replacing `_proof_2` with the direct canonical `IsRightCancelAdd Int` provider. All three local expressions passed `checkWithKernel`. D1 and D2 are structurally different from D0 and each other; their reconstructed closed-type DefEq calls returned true below 1 ms. The fresh original root's direct `_proof_2` comparison is one call, 0.005 ms exclusive. This does not measure `_proof_2`'s possible effect on dependent `whiskerRight`, `map`, or `map_comp` in the expensive original root. [K,R,U]

`D'` type alias exposure is a distinct layer from the `MC-D'` instance and the generated D adapter. The fresh extracted category-type pair is structurally equal, DefEq true in less than 1 ms, and has the same Expr hash on both sides. WHNF of that common category expression exposes the quotient target. The alias has regular hint 2 and returns `D`; the provider applications and WHNF structure fields remain unequal. The measured expensive path is therefore associated with the instance/provider expressions, while an independent causal share for the wrapper instance or D adapter has not been isolated. [A,C,I,U]

## 6. Same-root cost and instrumentation (§5-§6/P6)

| Layer | Calls | Same-root exclusive time | Reduction-exclusive time | Classification |
| --- | ---: | ---: | ---: | --- |
| Full twelve-binder root | 6,239,533 | 62.349 s | 21.709 s | direct exact-source replay [R] |
| `U.map` path | not separately exported | 18.584 s subtree | not separately exported | same-root path [R] |
| `U.map_comp` path | not separately exported | 42.407 s subtree | not separately exported | same-root path [R] |
| `U.obj` path | not separately exported | 0.524 s subtree | not separately exported | same-root path [R] |
| `U.map_id` path | not separately exported | 0.831 s subtree | not separately exported | same-root path [R] |
| `MC-D` / `MC-D'` delta heads | 3 aggregate unfolds | 0.065 ms delta only | included at root | not a provider-subtree partition [R] |
| `MC-K-shortcut` / canonical delta heads | 3 aggregate unfolds | 0.096 ms delta only | included at root | not a K-subtree partition [R] |
| `tensorObj`, `whiskerRight`, `whiskerLeft`, generic field, target Hom, Q map, other | no disjoint export | unknown | unknown | nested/overlapping [U] |

The four `Functor.mk` field paths are disjoint in the path summary; their subtree times are *inclusive of their own descendants* and are not added to child replays. The `map_comp` route enters `Functor.uncurry._proof_3`'s proposition type; its Eq RHS and LHS subtrees are 22.486 s and 18.806 s within the 42.407 s path. The `map` route includes target composition and `NatTrans.app`/`whiskerRight`; the original-root recorder does not export a non-overlapping `whiskerRight` charge. [R,U]

The reduced event file retains the READY4.2 IDs, branch, side, hashes, pre/post heads, first-divergence path and exclusive/reduction time for selected calls. The requested extended semantic-layer schema, full Expr dumps/types/ordinary arguments at *every* provider event, and all reduction callers were not produced by the existing observational recorder. Those fields are covered partially by the declaration and child probes and otherwise marked unknown, rather than inferred. [R,A,U]

## 7. Decision criteria and remaining uncertainty (§9-§10)

**Outcome G: inconclusive for causal attribution.** The declaration audit proves the D adapter is a genuine earlier structural divergence and consumes `MC-D'` through `_aux_1`; the new root confirms K canonical/shortcut exposure and an expensive downstream `map`/`map_comp` path. D-route substitutions are Kernel-valid, but the canonical K application copied from the checked provider is not valid in the stored original closed binder graph: its bound-variable dependencies do not match that context. The controlled local/closed pairwise replays did not reproduce the original expensive root, while the expensive `checkWithKernel` runs measured validation of rebuilt expressions rather than the controlled original-root DefEq. No outcome A, B, C, D, E, or F is established as a cost-causal result. [A,R,K,U]

The specific next measurement needed is an M0-shaped twelve-binder `Kernel.isDefEq` comparison that remains expensive under the baseline harness, followed by the same invocation and event schema for C10, C01, C11, D1, and D2. The unreduced checked shortcut application and its eight ordinary arguments also need direct capture; without them no claim that the two K applications are identical before reduction is justified. [U]

`sdtdcp/` contains only reduced data and probes. Every file is below 5 MB; the 34 MB bounded scratch trace was not copied. No absolute machine path or address was placed in repository files. No commit or push was made. [A]
