# Mismatch Provenance and Recursive Workload Report

Case: RealPushforward
Lean / Mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; READY2-4.35.0.
Instrumentation: observational READY2 counters and capped path trace; no READY3 provenance build was available during this run.

## 1. Root mismatch

Root conversion: final polynomial equality conversion.
Exact pair summary: local Frobenius polynomial versus charpolyRev representation; path Matrix.charmatrix -> DFunLike.coe -> ContinuousMap
The root mismatch is M0 by the plan's operational definition. This report does not revisit the established trigger or unfolding choice.

## 2. Matched baseline

Baseline level: A3 diagnostic. The matched probe uses a smaller operation or component obligation and does not preserve the full dependent consumer.

| Probe | Measured result |
|---|---|
| O | 52.021 s / 17,340,236 calls; comparison 52.018 s; WHNF 0.0029 s; depth 91 |
| M | 0.030 ms / 15 calls; comparison 0.027 ms; reduction 0.003 ms; depth 6 |
| A | no expensive root after polynomial alignment |
| R | 53.628 s / 17,340,236 calls; comparison 53.625 s; WHNF 0.0029 s |

The fresh M probe typechecked with full Kernel checking and performed a non-identity conversion. It is not A0/A1. The exact source pair and audit are in probes/mprwe/{Matched,Original,Aligned,Restored}.lean.

## 3. Provenance distribution

READY2 records recursive counts, branch/depth histograms, inclusive path samples, and root timers, but not parent-child IDs, reduction predecessors, local-context fingerprints, or semantic first divergences. Exclusive provenance attribution is therefore intentionally Unclassified.

| Provenance | Recursive calls | Exclusive comparison time | Status |
|---|---:|---:|---|
| M0 | not separable | not separable | root entry identified |
| M1 | not separable | not separable | M0 is the polynomial representation. Downstream Matrix.charmatrix/DFunLike.coe tree may be M2 or matched intrinsic work; READY2 cannot decide. |
| M2 | not separable | not separable | no reduction event recorded |
| Matched descendants | not separable | not separable | no context-aware pair identity |
| Unclassified | all O calls | all O comparison time | measured remainder |

Root partitions are not summed with inclusive child path samples. Trace path labels are qualitative and do not constitute exclusive attribution.

## 4. Newly exposed divergences

No major M2 can be established at call-node granularity with READY2. M0 is the polynomial representation. Downstream Matrix.charmatrix/DFunLike.coe tree may be M2 or matched intrinsic work; READY2 cannot decide. The reduction that immediately preceded a candidate M2, its call ID, and its descendant fan-out are unavailable. Orthogonal dependent/proposition tags are available only as overlapping aggregate timers in inherited AD/IM records.

## 5. Selective descendant alignment

O1-polynomial-aligned removes M0 and is invalid for C. No descendant-only alignment preserving the polynomial root was available. R restores the root.

Every copied source snapshot is under probes/mprwe/; none modifies the library.

## 6. Conclusion

Outcome E: comparison-heavy downstream work is real, but its provenance remains unclassified.

Matched intrinsic cost: only the A3 diagnostic cost is measured; it must not be generalized to O.
Inherited M1 cost: plausible in the dependent paths above, but quantitatively unclassified.
Newly exposed M2 cost: unclassified; no causal M2 intervention is valid.
Unclassified share: 100% of the O recursive-call and exclusive-time attribution for this phase.
Remaining uncertainty: a READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

## MPRWE round 2 (READY3.1)

The non-identity A3 matched probe used 15 calls, 0.027 ms comparison-exclusive and 0.003 ms reduction-exclusive (0.030 ms wall).

### B. Original provenance

Root 2005 has complete aggregate coverage: 17,340,236 calls and 75,988.013 ms comparison-exclusive time. A selected raw rerun captured 3,122 traced calls and 10,000 raw events; representatives include `Scheme.Hom.toLRSHom`, `Scheme.Hom.proj`, `ContinuousMap.comp`, and `CategoryTheory.Limits.IsLimit.proj` versus `CategoryTheory.Iso.proj`.

| Category | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.014 | 0.000% |
| M1 | 8,002,209 | 46,710.171 | 61.473% |
| M2 | 4,364,762 | 28,270.299 | 37.204% |
| Matched | 4,973,262 | 1,007.514 | 1.326% |
| Unclassified | 2 | 0.014 | 0.000% |

### C. Intervention and restoration

`O1-polynomial-aligned` removes the root and completes in 1 call / 0.014 ms comparison-exclusive; it is invalid as selective C. The supplied restoration is a 3-call / 0.075 ms comparison control and does not reproduce O.

### 9. Outcome

**Outcome D (mixed M1/M2 amplification).** M2 contributes 37.204% of exclusive time. The raw representatives show substantial projection/coercion descendants, but no type-correct M0-preserving C intervention was available.

## MPRWE round 3 (READY3.2)

Root identity and analysis are corrected; shares are M1 61.473%, M2 37.204%,
Matched 1.326%, Unclassified 0.000%. The polynomial replacement remains
root-changing.


## MPRWE round 4 (READY3.2; supersedes round 2/3 figures)

Analyzer: READY3.2 mprwe_analyze.py; revision 2e92d5989ff. The pinned expensive root is 2005; helper root 2003 (2,873 calls) is excluded. Counter O root 2005: 17,340,236 calls / 125,356.436 ms comparison-exclusive (the run records the root before its deterministic timeout). Pinned trace root 2005 has 17,340,236 calls / 105,827.556 ms aggregate exclusive; raw coverage 3,122 calls (0.018%) and 32.981 ms (0.031%). The helper run exposed the same 17,340,236-call aggregate root; helper root was 2,873 calls / 11.772 ms.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.018 | 0.000% |
| M1 | 8,002,209 | 66,683.369 | 63.011% |
| M2 | 4,364,762 | 38,082.400 | 35.985% |
| Matched | 4,973,262 | 1,061.742 | 1.003% |
| Unclassified | 2 | 0.028 | 0.000% |

M0 is the root entry; no separate raw child was captured under the cap. Top raw review: M1 AlgebraicGeometry.Scheme.Hom.toLRSHom, SMul.smul, 6, HSMul.hSMul, another 6; M2 CategoryTheory.Limits.IsLimit.proj versus CategoryTheory.Iso.proj, AlgebraicGeometry.Scheme.Hom.proj, and three AlgebraicGeometry.LocallyRingedSpace.Hom.proj versus CategoryTheory.CategoryStruct.comp nodes, exposed by initial_whnf; Matched AlgebraicGeometry.Scheme.toLocallyRingedSpace, ContinuousMap, ContinuousMap.mk, TopCat.carrier, FrobeniusModule.module; Unclassified has two tiny 7 versus 5 entries.

C: polynomial alignment changes the final dependent consumer and restoration is not O. No M0-preserving descendant control type-checks; the polynomial/charpolyRev consumer is the obstruction. Outcome D.
