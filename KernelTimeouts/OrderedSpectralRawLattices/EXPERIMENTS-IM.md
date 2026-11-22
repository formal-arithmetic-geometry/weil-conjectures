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
