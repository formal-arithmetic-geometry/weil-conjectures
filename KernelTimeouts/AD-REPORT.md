# Targeted DefEq Follow-up Report

Dataset: `KernelTimeouts` follow-up experiments from AD-TASK.
Lean 4.35.0: `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
READY2-4.35.0 records component paths, exclusive dependent/proposition
timers, C++ Expr constructor counts/bytes, and RSS/commit deltas. It does not
record local-context identity or a GC timer; proposition timers can overlap
recursive and WHNF spans. Historical 4.33.1 profiles use READY2-4.33.1.

## Results

| Case | Experiment | Original measured root | Control/restoration | Result |
|---|---|---:|---:|---|
| EtaleHomComparisonReversedExact | C: instantiated `hv` proposition | READY2 counters 24.140 s; 3.180M calls; 12.301 s comparison / 11.839 s reduction | aligned: no root >100 ms; restored 81.640 s / 9.535M calls | dependent proposition path and allocation measured |
| FiniteBaseChangeRestrictionMateTransport | C: `hb` Site/Quiver.Hom proposition | READY2 counters 661.952 s; 239.341M calls; 661.896 s comparison | aligned: 116 ms setup root; restored 646.663 s | 99.6% of root partition in dependent labels; 2.960B Exprs |
| F66Adj | C: argument-39 counit proposition | READY2 counters 29.544 s; 3.898M calls; 15.058 s comparison / 14.486 s reduction | aligned: no root >100 ms; restored 76.595 s / 9.536M calls | `hR` proof representation is causal |
| ImageHomCounit | A: raw/wrapper derived-category endpoint | READY2 counters 50.730 s; 6.360M calls; wrapper-only 75.453 s / 9.539M calls | aligned 0.058 ms root; restored 48.764 s | endpoint bundle path is causal; wrapper-only is a negative isolation control |
| IntegralComparisonPullbackRealizationShifts | A/C: downstream `change` endpoint | READY2 counters 73.839 s; 9.426M calls; 44.816 s comparison / 29.024 s reduction | downstream trace 88.313 s; first-instance rerun invalid (`HeadAuditTools` missing) | nested `NatTrans.app` path dominates; first leaf remains negative |
| RealPurity | A/C: rewritten equality proposition | READY2 counters 53.956 s; 17.310M calls; 53.949 s comparison | downstream diagnostic 67.955 s; ring alignment no expensive root | `DFunLike.coe`/`Matrix.charmatrix` path dominates |
| RealPushforward | A/C: polynomial equality proposition | READY2 counters 52.072 s; 17.340M calls; 52.069 s comparison | polynomial alignment no root >100 ms | comparison-heavy `Matrix.charmatrix`/`DFunLike.coe` path |
| OrderedSpectralRawLattices | A/B/C bundle follow-up | READY2 trace 51.962 s; 18.945M calls; 51.938 s comparison | all-route aligned no root >100 ms; partial restores 35.939--36.282 s | complete R/H/D bundle remains the only valid ablation |
| Historical Derived-Completion Cone | A/C: inline final dependent conversion | READY2 counters 103.297 s timeout root; 12.221M calls; 51.471 s comparison / 51.826 s reduction | path trace 123.761 s; 602.996M Exprs | `tensorLeft`/`Functor.obj` dependent body dominates; 36 outer proof positions are cheap in isolation |
| Historical SlowDerivedTensor | B attempt: shared vs independent `MonoidalCategoryStruct` | READY2 profile: 42.201 s counters; path trace 55.322 s | shared-binder declaration no root >100 ms; 239.0M Exprs independent | invalid fixed-root control; no causal sharing claim |

## Dependent comparison (C)

The READY2 dependent labels make the split explicit. Etale and F66 have mixed
comparison/reduction roots, while FiniteBaseChange has 239 million calls and
170.6 million failed/stuck attempts with 659.1 s in the dependent partition.
Image and Integral also spend most of their root partition in dependent
subtrees. The transport controls remove the corresponding instantiated
proposition while preserving the consumer and theorem obligation. Direct
instantiation time is small compared with the dependent body; proposition
timers remain overlapping diagnostics.

## Targeted A controls

ImageHomCounit supplies the cleanest reversible A result. Full alignment of
all derived-category endpoints reduces the same final `exact h` from the
large root to a millisecond-scale control; expanding only the wrapper makes
the root larger, so the outer wrapper is not the sole expensive component.

IntegralComparison is a negative A control. Aligning the first
`HasDerivedCategory` instance moves the first visible mismatch but leaves the
deep presheaf/module/functor bundle. A one-factor C replacement would change
the dependent `change` target, so it is invalid.

RealPurity and RealPushforward share a strong measured trace signature. Their
partial roots have nearly identical call counts and top children at
`DFunLike.coe`, `ContinuousMap.proj`/`Function.comp`, `ContinuousMap.comp`,
and `Eq.ndrec`. The common result is an expression-head family, not a claim
that one exact ordered pair is shared; local context is not in the pair key.
RealPurity's ring-leaf alignment leaves the timeout unchanged, rejecting the
ring leaf as the dominant component. A raised-budget diagnostic at 400,000
heartbeats ran for 118.17 s and still timed out; its later unknown-constant
error is the expected cascade from the failed private theorem, so it is not
used as a completed root measurement.

Within OrderedSpectral, the complete R/H/D alignment is the only valid
ablation unit:
single-route and pair controls all time out, while the all-route control
aligns both repeated ring-object values and succeeds. A shared-provider B
matrix cannot preserve the imported theorem's elaborated instance arguments,
and a dependent-field C harness either does not enter the consumer or changes
the root obligation. Both are explicitly rejected rather than replaced by a
synthetic structure.

The historical SlowDerivedTensor provider matrix is not a valid fixed-root B
experiment. Two independently supplied providers remain expensive even when
their construction path is the same, while one shared local provider enters
no reportable root. The READY2 validity rerun shows why: the shared declaration
adds an `MC` instance binder and changes the inferred/declared type sizes from
5,361/18,817 to 2,283/3,917. Its direct meta checks therefore run after the
original conversion has been removed. The counters measured about 238 million
expression creations for the independent variants, but this is only a
correlate; no causal sharing estimate is assigned.

## Measurement limits

READY2 trace overhead ranged from 19.6% (Integral downstream) to 31.9%
(Etale); the historical 4.33.1 controls report their own overhead in the
case records. C++ Expr counts/bytes are constructor proxies, not complete
heap allocation or GC measurements. RSS/commit deltas are process proxies.
The finite READY2 detailed trace completed under the same 3,600-second limit;
its 776.225 s root and `NatTrans.app` path are recorded in the case record.

Per-case source probes and compact diagnostic logs are under each case's
`probes/sa/r2/` and `probes/ad/`; compact first-pass traces remain under
`probes/anatomy/`.
