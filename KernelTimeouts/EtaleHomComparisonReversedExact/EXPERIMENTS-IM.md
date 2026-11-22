# Intrinsic vs mismatch-induced DefEq report

Case: `EtaleHomComparisonReversedExact`
Lean/Mathlib: Lean 4.35.0, current-case tree revision `a2ec460045b`, READY2-4.35.0.
Root: instantiated argument 26 (`hv`) of `derivedTensorHomShiftComparison_component`.
Branch baseline: `5ece8b` before this IM work.

## Variants and pairs

O/A/R are `probes/im/{Original,Aligned,Restored}.lean`. A transports the whole expected `hv` proposition; R exposes the named predicate while retaining the original domain mismatch. A strict M is unavailable: replacing `hv` by a proof with the same mismatched type does not remove the representation divergence, while transporting it is A.

## Kernel cost

Measured READY2 baselines: O 24.140 s, 3,180,470 calls, 12.301 s comparison, 11.839 s reduction, depth 111, 140,620,668 Expr constructions / 4,699,706,856 B. A had no root over 100 ms (largest 83.711 ms, 7,014 calls). R returned 81.640 s, 9,535,141 calls, and 421,570,091 Expr constructions / 14,089,375,944 B. O had 132,807 Pi-domain events, 412,714 instantiations, and 1,046,492 exact repeats in the capped trace.

The trace root was 31.825 s. The dominant inclusive path was `DFunLike.coe -> NatTrans.app` under `binder_body[1]/argument[2]`, with 31,817 ms; `tensorLeft` proposition children contributed 14,395 ms and the `Quiver.Hom` child 9,034 ms. These are inclusive path samples.

## Operation and unification analysis

The `.app` and `DFunLike.coe` branches expose the dependent proposition body; the patch does not provide exclusive operation time. The imported theorem has already selected all critical implicit providers. The attempted generic hint was rejected as mechanical and the source tree currently lacks additional dependency oleans for a safe U1 replay; no unif_hint Kernel claim is made.

## Conclusion

**H2 mismatch-induced for the instantiated `hv` proposition; operation H1 unresolved.** A/R establish reversibility at the whole proposition. A valid M requires a non-identical same-representation `hv` premise in the same telescope.
