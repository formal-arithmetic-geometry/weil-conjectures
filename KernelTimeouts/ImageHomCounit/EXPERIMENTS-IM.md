# Intrinsic vs mismatch-induced DefEq report

Case: `ImageHomCounit`
Lean/Mathlib: Lean 4.35.0, current-case tree revision `a2ec460045b`, READY2-4.35.0.
Root: final `exact h` conversion for `conjugateEquiv_counit`.
Branch baseline: `5ece8b` before this IM work.

## Variants and expression pairs

- **O:** `probes/im/Original.lean`, raw endpoint equality.
- **A:** `probes/im/Aligned.lean`, all raw/wrapper derived-category endpoints aligned while retaining the same `h` and consumer.
- **R:** `probes/im/Restored.lean`, wrapper-only restoration with the inner endpoint mismatch left in place.
- **M diagnostic:** `probes/im/MatchedLet.lean` wraps the left side in a `let` and audits the elaborated pair.

The M audit measured `syntactic=false` for the equality operands, but also showed `DerivedCategory` versus `DerivedCategoryModule` at the endpoint arguments. The `let` is therefore not a matched representation: the original divergence remains. It is invalid as M.

## Kernel cost

O/A/R are measured READY2-4.35.0 baselines from the same snapshots. The M source audit run itself took 53.77 s wall, 52.73 s user, and 7,704,540 KB peak RSS; it was a release run, not a counters profile.

| Variant | Root time | DefEq calls | Comparison excl. | WHNF excl. | Max depth | Expr proxy |
|---|---:|---:|---:|---:|---:|---:|
| O | 50.730 s | 6,359,958 | 25.076 s | 25.655 s | 204 | 281,230,787 / 9,398,990,560 B |
| M | invalid diagnostic | - | - | - | - | source RSS 7,704,540 KB |
| A | no root >100 ms; largest 0.016 s | 2,881 | - | - | - | none at root |
| R | 75.453 s | 9,539,325 | 37.416 s | 38.037 s | - | 421,726,792 / 14,094,527,488 B |

O entered 265,526 Pi domains and 825,116 instantiations. The trace root was 62.200 s; the dominant inclusive path was `Functor.map -> NatTrans.app -> DFunLike.coe` under `binder_body[6]/argument[1]`, with 62,183 ms in the deepest repeated `.app` subtree. O had 1,644,449 exact repeats in the capped trace. R is a negative isolation control: exposing only the outer wrapper is more expensive than O.

## Operation analysis

The `Functor.map` and `NatTrans.app` branches are path markers. The measured root partition is mixed comparison/WHNF, and the `NatTrans.app` path owns inclusive descendant time, not proven exclusive operation time. A removes the complete endpoint bundle and the root; R preserves the inner mismatch and remains expensive.

No genuine source-level `unif_hint` experiment is claimed. The endpoint choice is already elaborated in the imported theorem; adding a hint would change the stored provider or the goal rather than preserve this root.

## Conclusion

**H2 mismatch-induced for the endpoint bundle; operation-level H1 unresolved.** Directly measured: O, A, R and the invalid M audit. A/R support causality of the full endpoint representation. The next falsifying control is a same-endpoint-provider, non-identical component equality; the available imported counit does not provide one.

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (O vs component M): 281,230,787 / 4,751,753,216 B versus 37,724 / 1,638,400 B. These are process proxies, not retained allocations.

Fresh runs: source head `03f2a41973c`, Lean/READY2-4.35.0, master `f21ef672d31` oleans plus targeted Stability rebuilds. `probes/im/Matched.lean` supplies two **diagnostic M** comparisons with the concrete `imageTensorIso A K T` and `ExternalRHom` providers on both sides: its `.hom.app` at the original endpoint object versus the same `.app` at a beta-expanded object, and the original `Functor.map (imageHomIso A M K T).hom` versus the same map at a beta-expanded morphism. Both end in `exact h` after a syntactically distinct `have h` type. O instead consumes `conjugateEquiv_counit` at the complete raw/wrapper endpoint equality, so M changes the root equality and removes the endpoint representation mismatch.

| Fresh READY2 counters | O | M `.app` | M `Functor.map` | A | R |
|---|---:|---:|---:|---:|---:|
| root wall / calls | 48,565.681 ms / 6,359,958 | 4.680 ms / 808 | 0.201 ms / 28 | no root >=100 ms | 75,891.192 ms / 9,539,325 |
| comparison / WHNF exclusive | 24,379.162 / 24,186.519 ms | 1.901 / 2.779 ms | 0.108 / 0.093 ms | no large root | 37,507.269 / 38,383.923 ms |
| max depth | 204 | 63 | 7 | - | 201 |

O branch comparison-exclusive: projection 1,370,691 calls / 15,326.563 ms; application 1,178,468 / 4,186.121 ms; second-WHNF 511,395 / 2,200.214 ms. The `.app` M has 30 projections / 0.267 ms, 114 applications / 0.242 ms, and 130 second-WHNF calls / 0.709 ms. Fresh O trace follows `CategoryStruct.comp -> DFunLike.coe -> Functor.map -> NatTrans.app/Iso.hom`; the `Functor.map` node has 85,614 ms inclusive subtree but only 0.110 ms direct exclusive time. The M `.app` root reaches `NatTrans.app -> CategoryStruct.comp -> DFunLike.coe` (5.430, 4.863, 3.408 ms inclusive); the map M runs 28 recursive calls. The difference is in descendants and the endpoint argument, not in a costly direct `Functor.map` branch. Final M source run: 2.84 s wall including import; O release time not rerun separately.

**Verdict: diagnostic H2 support; strict intrinsic classification inconclusive.** O/A/R show the endpoint bundle is causal, and M's same-provider component and map conversions are cheap. Their root equalities are smaller than O, so the roughly 7,871-fold O/M component call gap cannot by itself allocate cost to the original mismatch rather than the removed dependent context. The old `MatchedLet` remains an invalid strict control and is retained above as history.
