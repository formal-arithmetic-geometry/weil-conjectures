# Mismatch Provenance and Recursive Workload Report

Case: RealPurity
Lean / Mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; READY2-4.35.0.
Instrumentation: observational READY2 counters and capped path trace; no READY3 provenance build was available during this run.

## 1. Root mismatch

Root conversion: final exact h conversion in rewritten hreal proposition.
Exact pair summary: local Frobenius polynomial equality with ring leaves; downstream Matrix.charmatrix -> DFunLike.coe -> ContinuousMap family
The root mismatch is M0 by the plan's operational definition. This report does not revisit the established trigger or unfolding choice.

## 2. Matched baseline

Baseline level: A3 diagnostic. The matched probe uses a smaller operation or component obligation and does not preserve the full dependent consumer.

| Probe | Measured result |
|---|---|
| O | 53.956 s / 17,310,168 calls; comparison 53.949 s; WHNF 0.0068 s; depth 93 |
| M | 0.045 ms / 15 calls; comparison 0.042 ms; reduction 0.003 ms; depth 6 |
| A | no expensive root after both ring leaves are aligned |
| R | 53.575 s / 17,310,168 calls; comparison 53.572 s; WHNF 0.0029 s |

The fresh M probe typechecked with full Kernel checking and performed a non-identity conversion. It is not A0/A1. The exact source pair and audit are in probes/mprwe/{Matched,Original,Aligned,Restored}.lean.

## 3. Provenance distribution

READY2 records recursive counts, branch/depth histograms, inclusive path samples, and root timers, but not parent-child IDs, reduction predecessors, local-context fingerprints, or semantic first divergences. Exclusive provenance attribution is therefore intentionally Unclassified.

| Provenance | Recursive calls | Exclusive comparison time | Status |
|---|---:|---:|---|
| M0 | not separable | not separable | root entry identified |
| M1 | not separable | not separable | M0 is the polynomial/ring representation boundary. The downstream DFunLike.coe/Matrix.charmatrix path could be M2 or matched intrinsic work; READY2 has inclusive heads only. |
| M2 | not separable | not separable | no reduction event recorded |
| Matched descendants | not separable | not separable | no context-aware pair identity |
| Unclassified | all O calls | all O comparison time | measured remainder |

Root partitions are not summed with inclusive child path samples. Trace path labels are qualitative and do not constitute exclusive attribution.

## 4. Newly exposed divergences

No major M2 can be established at call-node granularity with READY2. M0 is the polynomial/ring representation boundary. The downstream DFunLike.coe/Matrix.charmatrix path could be M2 or matched intrinsic work; READY2 has inclusive heads only. The reduction that immediately preceded a candidate M2, its call ID, and its descendant fan-out are unavailable. Orthogonal dependent/proposition tags are available only as overlapping aggregate timers in inherited AD/IM records.

## 5. Selective descendant alignment

O1-left-ring-restored and ring-leaf alignment retain timeout-scale work but move the first divergence. They are invalid for a causal M2 test. R restores O.

Every copied source snapshot is under probes/mprwe/; none modifies the library.

## 6. Conclusion

Outcome E with a measured negative ablation: ring alignment does not remove the workload. The remaining downstream category is unclassified.

Matched intrinsic cost: only the A3 diagnostic cost is measured; it must not be generalized to O.
Inherited M1 cost: plausible in the dependent paths above, but quantitatively unclassified.
Newly exposed M2 cost: unclassified; no causal M2 intervention is valid.
Unclassified share: 100% of the O recursive-call and exclusive-time attribution for this phase.
Remaining uncertainty: a READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

## MPRWE round 2 (READY3.1)

The non-identity A3 matched probe used 15 calls, 0.027 ms comparison-exclusive and 0.003 ms reduction-exclusive (0.030 ms wall).

### B. Original provenance

Root 5100 has complete aggregate coverage: 17,310,168 calls and 76,192.584 ms comparison-exclusive time. A selected raw rerun captured 3,222 traced calls and 10,000 raw events; its top representatives were `AlgebraicGeometry.Scheme.Hom.toLRSHom` (M1), `CategoryTheory.Limits.IsLimit.proj` versus `CategoryTheory.Iso.proj` (M2), `LinearEquiv.proj`, `AlgebraicGeometry.PresheafedSpace.comp`, and `DFunLike.coe`.

| Category | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.008 | 0.000% |
| M1 | 7,988,264 | 47,271.645 | 62.046% |
| M2 | 4,357,093 | 27,862.546 | 36.568% |
| Matched | 4,964,810 | 1,058.386 | 1.389% |
| Unclassified | 0 | 0.000 | 0.000% |

### C. Intervention and restoration

`O1-left-ring-restored` reaches the deterministic timeout and then the unknown constant `AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`; ring alignment therefore moves/fails the root and is invalid as selective C. The supplied restoration has the same timeout/unknown-constant failure.

### 9. Outcome

**Outcome D (mixed M1/M2 amplification).** M2 is 36.568% of exclusive time, with raw representatives showing projection and coercion work. No type-correct M0-preserving descendant intervention was available, so the causal C effect is not separately estimated.

## MPRWE round 3 (READY3.2)

The prior restoration failure was a probe setup failure: the missing theorem
import and unknown constant were repaired in the restoration snapshot. The
restoration now reaches the recorded root; shares remain M1 62.046%, M2
36.568%, Matched 1.389%, Unclassified 0.000%.


## MPRWE round 4 (READY3.2; supersedes round 2/3 figures)

Analyzer: READY3.2 mprwe_analyze.py; revision 2e92d5989ff. Counter O: 17,310,168 calls / 52,925.953 ms comparison-exclusive. Pinned root 13603: 17,310,168 calls / 85,908.939 ms aggregate exclusive; raw coverage 3,222 calls (0.019%) and 35.756 ms (0.042%). Calls match.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.015 | 0.000% |
| M1 | 7,988,264 | 54,699.657 | 63.672% |
| M2 | 4,357,093 | 30,187.585 | 35.139% |
| Matched | 4,964,810 | 1,021.681 | 1.189% |
| Unclassified | 0 | 0.000 | 0.000% |

M0 is the root entry; no separate raw child was captured under the cap. Top raw review: M1 AlgebraicGeometry.Scheme.Hom.toLRSHom, CategoryTheory.ObjectProperty.FullSubcategory.proj, DFunLike.coe, LinearEquiv.proj, AlgebraicGeometry.PresheafedSpace.comp; M2 CategoryTheory.Limits.IsLimit.proj versus CategoryTheory.Iso.proj, AlgebraicGeometry.Scheme.Hom.proj (two), and AlgebraicGeometry.LocallyRingedSpace.Hom.proj versus CategoryTheory.CategoryStruct.comp, exposed by initial_whnf; Matched AddCommGroup.toAddCommMonoid, Semiring.toModule, TopCat.carrier, Eq, ContinuousMap.

C: ring-leaf alignment changes the dependent real-purity witness telescope; no M0-preserving descendant control type-checks. Outcome D.
