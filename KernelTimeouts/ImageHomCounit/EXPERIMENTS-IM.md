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
