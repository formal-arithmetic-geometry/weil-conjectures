# Intrinsic vs mismatch-induced DefEq report

Case: `OrderedSpectralRawLattices`
Lean/Mathlib: Lean 4.35.0, source snapshot `f4946fdb6b6`, READY2-4.35.0.
Root: final conversion from `exists_stratified_lisse_integral_lattice` to `RawStratifiedLattices`.
Branch baseline: `5ece8b` before this IM work.

## Variants and cost

O/A/R are `probes/im/{Original,Aligned,Restored}.lean`. O uses competing regular/Henselian/domain routes; A aligns all three; R restores the domain route. A strict M and a shared-provider control are invalid because local provider availability changes the stored theorem or dependent lattice predicate.

Measured READY2 O: 51.962 s, 18,944,709 calls, 51.938 s comparison, 0.024 s reduction, 2,928,324 instantiations, 213,249,957 Expr constructions / 6,975,943,792 B. A entered no root over 100 ms. R/domain restoration returned about 35.939 s with about 18.945M calls and the same Expr scale; Henselian partial restores timed out before a comparable root.

The dominant inclusive path is `binder_body[17]` through nested `Exists`/`Quiver.Hom` into `Functor.obj`/`Mod.X`, carrying 51,909 ms. The branch is comparison-dominated; no exclusive `Functor.obj` time is available.

## Unification and conclusion

No `unif_hint` is included. The R/H/D route choice is an instance-provider selection already fixed in the imported theorem; a hint would change the provider and fail U2’s fixed-expression requirement. **H2/H3 bundle interaction:** A proves the complete route bundle is causal, while partial restoration remains expensive. Intrinsic `Functor.obj` cost is not isolated.

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (O vs M): 213,249,957 / 796,983,296 B versus 2,665 / 65,536 B. These are process proxies, not retained allocations.

Fresh runs use source head `03f2a41973c`, READY2-4.35.0, and master `f21ef672d31` oleans plus targeted Stability rebuilds. `probes/im/Matched.lean` is a **diagnostic M** in the original coefficient-module family: `(CondensedRing.upperStar A f).obj M` versus the same `Functor.obj` applied to `((fun Z => Z) M)`. Both sides use the same upper-star provider and module object; a local `have h` consumed by `exact h` has a syntactically different elaborated type. O is the much larger `RawStratifiedLattices`/`Exists` proposition with competing R/H/D routes, so the consumer and root proposition change.

| Fresh READY2 counters | O | M | A | R |
|---|---:|---:|---:|---:|
| root wall / calls | 36,145.418 ms / 18,944,709 | 0.309 ms / 84 | no root >=100 ms | 36,313.310 ms / 18,944,728 |
| comparison / WHNF exclusive | 36,125.432 / 19.986 ms | 0.168 / 0.142 ms | no large root | 36,292.949 / 20.361 ms |
| max depth | 71 | 18 | - | 71 |

O's failure branch consumes 8,421,981 calls / 32,754.160 ms comparison-exclusive; lazy delta is 726,153 / 2,751.974 ms. M has no failure branch; its `Functor.obj` child has 0.412 ms inclusive and 0.075 ms direct exclusive in the fresh trace. The O trace follows `Exists`/`Quiver.Hom` into `Functor.obj`; that path remains inclusive, while the failure branch accounts for most exclusive time. O and R hit the Lean deterministic timeout at the stored declaration. Final M source run was 2.31 s wall including imports; no separate O release timing was run.

**Verdict: diagnostic H2 support; strict M-versus-O verdict inconclusive.** A eliminates the whole route mismatch and R restores the 18.945M-call failure tree, but this small same-provider `Functor.obj` equality does not preserve the dependent lattice proposition. It establishes a cheap non-identical object-map conversion, not a bound on every matched `RawStratifiedLattices` comparison. The route providers are fixed in the imported theorem; no source-level `unif_hint` controls an independent unification assignment here.
