# Intrinsic vs mismatch-induced DefEq report

Case: `F66Adj`
Lean/Mathlib: Lean 4.35.0, current-case tree revision `a2ec460045b`, READY2-4.35.0.
Root: instantiated argument-39 counit proposition.
Branch baseline: `5ece8b` before this IM work.

## Variants and pairs

O/A/R are `probes/im/{Original,Aligned,Restored}.lean`. A transports only the `hR` proof representation; R restores the expensive `hR` form while changing the preceding tensor-isomorphism argument. A strict M cannot be constructed from the imported helper without changing its stored implicit provider, so no M timing is claimed.

## Kernel cost

Measured READY2 baselines: O 29.544 s, 3,897,905 calls, 15.058 s comparison, 14.486 s reduction, depth 121, 170,987,170 Expr constructions / 5,714,525,816 B. A entered no root over 100 ms (largest 26.484 ms, 2,881 calls). R returned 76.595 s, 9,536,477 calls, and 421,630,510 Expr constructions / 14,091,341,096 B. O had 176,636 Pi-domain events, 531,910 instantiations, and 1,290,616 exact repeats in the capped trace.

The trace root was 38.829 s. Its dominant inclusive path was nested `DFunLike.coe -> NatTrans.app`, with 34,886 ms in the deepest `.app` subtree; `tensorHomAdjunctionQhObj` and the derived monoidal proof were smaller children (2,026 ms and 1,899 ms).

## Operation and unification analysis

`DFunLike.coe`/`NatTrans.app` are path markers; the root partition is mixed dependent comparison and reduction. A removes the instantiated dependent proposition; R restores it. A tautological `Functor.obj` hint would be mechanical, so no unif_hint file is included: the source has no isolatable metavariable assignment that preserves argument 39 and its consumer.

## Conclusion

**H2 mismatch-induced, with descendant attribution.** The `hR` representation drives the measured tree; intrinsic `.app` cost is not established. A valid M would require a second non-identical counit proposition using the same provider, which is unavailable in the imported theorem.
