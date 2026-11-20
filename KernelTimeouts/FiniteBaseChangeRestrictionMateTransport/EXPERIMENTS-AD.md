# DefEq Internal Cost Experiments

Case: `FiniteBaseChangeRestrictionMateTransport`
Lean: 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
Root: dependent argument 49 (`hb`) in the `Site`/`Quiver.Hom` proposition.
Instrumentation: observational counters/trace build; diagnostic controls from the same source snapshot.

## C1: Original instantiated domain

Baseline root: `original.lean`. Counters measured 813.972 s root wall, 239,340,712 recursive calls, maximum depth 87, 813.896 s comparison-exclusive and 0.076 s WHNF-exclusive. There were 686 Pi-domain events and 3,293 proposition comparisons. The trace sample contained 3,534,109 repeated exact entries and 6.144 s sampled immediate repeated-pair time. The root is comparison-dominated; 170,625,719 calls failed or became stuck before the deterministic successful result.

The dominant measured shape is a very large recursive proposition comparison. The trace's largest children include `DFunLike.coe`, `Eq.ndrec`, `ContinuousMap.comp`, and repeated numeric structure fields. The high Delta event count is not a reduction-time explanation: the exclusive WHNF timer is 0.076 s.

## C2: Whole-bundle transport

Control: `aligned-Transport.lean`, transporting the complete `hb` proposition while retaining the same consumer and dependent telescope. The release diagnostic completed in 4.40 s; with threshold zero every recorded conversion was below 100 ms (largest 164.117 ms, 19,783 calls). This is a valid whole-proposition control, not an isolated argument replacement.

## C3: Restored original domain

Restoration: `restored.lean`. The diagnostic replay took 605.06 s wall (603.32 s user, 1.78 s system) and reached the original 23.9 GB RSS scale. The run returned the same successful theorem result; it is a high-overhead restoration measurement, not a replacement for the counters-only baseline.

## Conclusion

The complete dependent `hb` proposition is causal for the comparison tree: transport removes hundreds of millions of recursive calls, while the restored proposition recreates the expensive work. The patch cannot assign exclusive time to individual `Site` or `Quiver.Hom` binders, and it has no allocation/GC accounting.

## READY2 round 2

The READY2-4.35.0 expensive root (the second root in the source file, after a small setup check) was 661.952 s with 239,340,712 calls, 661.896 s comparison-exclusive time, and 55.948 ms reduction-exclusive time. It had 686 Pi-domain events and 40,293,390 instantiations. Dependent comparison/reduction was 659.077 s / 45 ms, so the root is comparison-dominated. The Expr proxy created 2,960,140,990 expressions / 96,645,705,328 bytes, with a 22,042,116,096-byte RSS/commit delta.

The restored original root was 646.663 s with 239,340,717 calls and 2,960,142,822 Expr constructions / 96,645,767,016 bytes. The aligned transport retained only the small setup root (116 ms, 678,893 Expr constructions); no expensive root was entered. The detailed original trace completed in 776.225 s (17.2% overhead over the counters root). Its dominant path was the dependent `CategoryStruct.comp` -> `LinearMap.comp` -> `PresheafOfModules.Hom.proj` -> repeated `NatTrans.app` chain under `root/binder_body[1]/argument[2]`; the deepest repeated `NatTrans.app` subtree carried 776,096 ms and 239,324,175 calls.
