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

## IM round 2

Fresh Expr-constructor/RSS-delta proxies (O vs component M): 140,620,668 / 2,373,976,064 B versus 19,415 / 589,824 B. These are process proxies, not retained allocations.

Fresh runs use source head `03f2a41973c`, Lean/READY2-4.35.0, and the master `f21ef672d31` oleans plus targeted Stability rebuilds. `probes/im/Matched.lean` has two **diagnostic M** obligations in the Etale context: `v.app (op K)` versus `v.app (op ((fun Z => Z) K))`, and `IsEtaleHomTranspose X φ M v` versus the same predicate at `((fun w => w) v)`. Both use the same `v`, scalar-extension route, and derived-module types on both sides. Each `exact h` consumes a syntactically different elaborated type and runs a recursive kernel conversion. O checks argument 26 (`hv`) of `derivedTensorHomShiftComparison_component`, so neither M preserves its full instantiated dependent telescope.

| READY2 counters | O, fresh | M `.app`, fresh | M proposition, fresh | A / R |
|---|---:|---:|---:|---|
| root wall / calls | 24,301.027 ms / 3,180,470 | 2.545 ms / 1,231 | 0.066 ms / 10 | A no root >=100 ms; R 32,154.489 ms / 3,179,834 |
| comparison / WHNF exclusive | 12,344.809 / 11,956.218 ms | 1.346 / 1.199 ms | 0.065 / 0.001 ms | R 15,801.221 / 16,353.268 ms |
| max depth | 111 | 34 | 2 | R 111 |

O's fresh branch distribution is projection 685,494 calls / 7,866.536 ms comparison-exclusive, application 589,257 / 1,947.590 ms, second-WHNF 255,588 / 1,127.723 ms. The component M has 19 projections / 0.240 ms, 82 applications / 0.162 ms, and 65 second-WHNF calls / 0.319 ms. Fresh trace: O's `IsEtaleHomTranspose -> DFunLike.coe -> CategoryStruct.comp -> NatTrans.app` child carries 45,812 ms inclusive below `DFunLike.coe`, whose direct exclusive time is 0.276 ms. M reaches the component's `Quiver.Hom` child (3.587 ms inclusive in trace); its other `.app` children are millisecond-scale. The proposition M is a shallow beta conversion, not a replay of the stored `hv` telescope. The final M uninstrumented run took 2.91 s wall including imports; no separate O release run was made.

The first A/R retry failed because `HomDevissage.olean` was temporarily absent from the read-only current tree. Once it reappeared, both completed: A removed the large root and R restored it. **Verdict: diagnostic H2 support; strict intrinsic-versus-mismatch classification inconclusive.** The O-to-M call gap is 2,584-fold for the `.app` control, but the obligations differ. The imported theorem has fixed providers, so no valid `unif_hint` kernel variant is available here.
