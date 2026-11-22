# Mismatch Provenance and Recursive Workload Report

Case: ImageHomCounit
Lean / Mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; READY2-4.35.0.
Instrumentation: observational READY2 counters and capped path trace; no READY3 provenance build was available during this run.

## 1. Root mismatch

Root conversion: final exact h conversion for conjugateEquiv_counit.
Exact pair summary: raw/wrapper derived-category endpoint equality; path Functor.map -> NatTrans.app -> DFunLike.coe
The root mismatch is M0 by the plan's operational definition. This report does not revisit the established trigger or unfolding choice.

## 2. Matched baseline

Baseline level: A3 diagnostic. The matched probe uses a smaller operation or component obligation and does not preserve the full dependent consumer.

| Probe | Measured result |
|---|---|
| O | 50.730 s / 6,359,958 calls; comparison 25.076 s; WHNF 25.655 s; depth 204 |
| M | 4.680 ms / 808 calls for app; 0.201 ms / 28 calls for Functor.map |
| A | no expensive root; largest threshold-zero root 16.251 ms |
| R | 75.891 s / 9,539,325 calls; comparison 37.507 s; WHNF 38.384 s |

The fresh M probe typechecked with full Kernel checking and performed a non-identity conversion. It is not A0/A1. The exact source pair and audit are in probes/mprwe/{Matched,Original,Aligned,Restored}.lean.

## 3. Provenance distribution

READY2 records recursive counts, branch/depth histograms, inclusive path samples, and root timers, but not parent-child IDs, reduction predecessors, local-context fingerprints, or semantic first divergences. Exclusive provenance attribution is therefore intentionally Unclassified.

| Provenance | Recursive calls | Exclusive comparison time | Status |
|---|---:|---:|---|
| M0 | not separable | not separable | root entry identified |
| M1 | not separable | not separable | M0 is the raw/wrapper endpoint bundle. app/Functor.map descendants are path markers; no exclusive provenance is available. |
| M2 | not separable | not separable | no reduction event recorded |
| Matched descendants | not separable | not separable | no context-aware pair identity |
| Unclassified | all O calls | all O comparison time | measured remainder |

Root partitions are not summed with inclusive child path samples. Trace path labels are qualitative and do not constitute exclusive attribution.

## 4. Newly exposed divergences

No major M2 can be established at call-node granularity with READY2. M0 is the raw/wrapper endpoint bundle. app/Functor.map descendants are path markers; no exclusive provenance is available. The reduction that immediately preceded a candidate M2, its call ID, and its descendant fan-out are unavailable. Orthogonal dependent/proposition tags are available only as overlapping aggregate timers in inherited AD/IM records.

## 5. Selective descendant alignment

O1-endpoint-aligned removes M0 and is invalid for C. Wrapper-only restoration remains expensive and is a negative isolation control. R restores the full raw endpoint.

Every copied source snapshot is under probes/mprwe/; none modifies the library.

## 6. Conclusion

Outcome E: endpoint bundle causality is measured; matched intrinsic versus M2 descendant cost is unresolved.

Matched intrinsic cost: only the A3 diagnostic cost is measured; it must not be generalized to O.
Inherited M1 cost: plausible in the dependent paths above, but quantitatively unclassified.
Newly exposed M2 cost: unclassified; no causal M2 intervention is valid.
Unclassified share: 100% of the O recursive-call and exclusive-time attribution for this phase.
Remaining uncertainty: a READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

## MPRWE round 2 (READY3.1)

The non-identity A3 matched probe used 28 calls, 0.102 ms comparison-exclusive and 0.088 ms reduction-exclusive (0.190 ms wall).

### B. Original provenance

Root 2129 has complete aggregate coverage: 6,359,958 calls and 42,708.813 ms comparison-exclusive time. A selected raw rerun captured 3,773 traced calls and 10,000 raw events; representatives include `DerivedCategory.tensorHomAdjunctionQhObj`, `DerivedCategory.instMonoidalCategory._aux_5`, and `CategoryTheory.Functor.proj`.

| Category | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.302 | 0.001% |
| M1 | 4,781,271 | 42,606.571 | 99.761% |
| M2 | 276 | 2.863 | 0.007% |
| Matched | 1,578,409 | 99.064 | 0.232% |
| Unclassified | 1 | 0.013 | 0.000% |

### C. Intervention and restoration

`O1-endpoint-aligned` removes the root and completes in 1 call / 0.083 ms comparison-exclusive; it is invalid as selective C. The supplied restoration completes at 9,539,325 calls, 37,162.499 ms comparison-exclusive and 38,321.502 ms reduction-exclusive, but is a distinct restoration source snapshot rather than a strict identity baseline.

### 9. Outcome

**Outcome C (M1 propagation).** M1 accounts for 99.761%; M2 is 0.007%. Raw representatives show ordinary downstream transport work, but no M2 cascade of material size.

## MPRWE round 3 (READY3.2)

Root identity and analysis are corrected; shares are M1 99.761%, M2 0.007%,
Matched 0.232%, Unclassified 0.000%. The endpoint replacement remains
root-changing.


## MPRWE round 4 (READY3.2; supersedes round 2/3 figures)

Analyzer: READY3.2 mprwe_analyze.py; revision 2e92d5989ff. Counter O: 6,359,958 calls / 42,138.453 ms comparison-exclusive. Pinned root 2129: 6,359,958 calls / 42,672.620 ms aggregate exclusive; raw coverage 3,773 calls (0.059%) and 34.133 ms (0.080%). Calls match.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.272 | 0.001% |
| M1 | 4,781,271 | 42,570.499 | 99.761% |
| M2 | 276 | 3.841 | 0.009% |
| Matched | 1,578,409 | 97.986 | 0.230% |
| Unclassified | 1 | 0.020 | 0.000% |

M0 is the root entry; no separate raw child was captured under the cap. Top raw review: M1 DerivedCategory.tensorHomAdjunctionQhObj, DerivedCategory.instMonoidalCategory._aux_5, CategoryTheory.ShrinkHoms.instCategory._proof_1, DerivedCategory.internalHomQhObj, DFunLike.coe; M2 CategoryTheory.Functor.proj (two), 6 versus AlgebraicGeometry.Etale.IndEtaleMapping.imagePullback._proof_5, and two more CategoryTheory.Functor nodes, exposed by initial_whnf; Matched 7 (two), AlgebraicGeometry.Etale.sheafMonoidalCategory, and two CategoryTheory.CategoryStruct.comp nodes.

C: endpoint alignment changes the dependent counit root and restoration is not O. No M0-preserving descendant control type-checks. Outcome C remains.
