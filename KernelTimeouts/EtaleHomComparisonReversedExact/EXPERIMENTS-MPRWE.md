# Mismatch Provenance and Recursive Workload Report

Case: EtaleHomComparisonReversedExact
Lean / Mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; READY2-4.35.0.
Instrumentation: observational READY2 counters and capped path trace; no READY3 provenance build was available during this run.

## 1. Root mismatch

Root conversion: instantiated argument 26 (hv) of derivedTensorHomShiftComparison_component.
Exact pair summary: IsEtaleHomTranspose under stored hv; path DFunLike.coe -> NatTrans.app -> tensorLeft
The root mismatch is M0 by the plan's operational definition. This report does not revisit the established trigger or unfolding choice.

## 2. Matched baseline

Baseline level: A3 diagnostic. The matched probe uses a smaller operation or component obligation and does not preserve the full dependent consumer.

| Probe | Measured result |
|---|---|
| O | 24.140 s / 3,180,470 calls; comparison 12.301 s; reduction 11.839 s; depth 111 |
| M | 2.545 ms / 1,231 calls (application diagnostic); proposition diagnostic 0.066 ms / 10 calls |
| A | no expensive root after whole-proposition transport |
| R | 81.640 s / 9,535,141 calls; restored diagnostic root |

The fresh M probe typechecked with full Kernel checking and performed a non-identity conversion. It is not A0/A1. The exact source pair and audit are in probes/mprwe/{Matched,Original,Aligned,Restored}.lean.

## 3. Provenance distribution

READY2 records recursive counts, branch/depth histograms, inclusive path samples, and root timers, but not parent-child IDs, reduction predecessors, local-context fingerprints, or semantic first divergences. Exclusive provenance attribution is therefore intentionally Unclassified.

| Provenance | Recursive calls | Exclusive comparison time | Status |
|---|---:|---:|---|
| M0 | not separable | not separable | root entry identified |
| M1 | not separable | not separable | M0 is the instantiated dependent proposition. Descendant DFunLike.coe/NatTrans.app is an inferred M1 candidate; M2 versus matched is unresolved. |
| M2 | not separable | not separable | no reduction event recorded |
| Matched descendants | not separable | not separable | no context-aware pair identity |
| Unclassified | all O calls | all O comparison time | measured remainder |

Root partitions are not summed with inclusive child path samples. Trace path labels are qualitative and do not constitute exclusive attribution.

## 4. Newly exposed divergences

No major M2 can be established at call-node granularity with READY2. M0 is the instantiated dependent proposition. Descendant DFunLike.coe/NatTrans.app is an inferred M1 candidate; M2 versus matched is unresolved. The reduction that immediately preceded a candidate M2, its call ID, and its descendant fan-out are unavailable. Orthogonal dependent/proposition tags are available only as overlapping aggregate timers in inherited AD/IM records.

## 5. Selective descendant alignment

O1-hv-aligned removes the same root mismatch and is invalid for C. No descendant-only alignment was constructible. R restores the expensive dependent tree.

Every copied source snapshot is under probes/mprwe/; none modifies the library.

## 6. Conclusion

Outcome E: whole-proposition transport is causal, but provenance shares are unavailable.

Matched intrinsic cost: only the A3 diagnostic cost is measured; it must not be generalized to O.
Inherited M1 cost: plausible in the dependent paths above, but quantitatively unclassified.
Newly exposed M2 cost: unclassified; no causal M2 intervention is valid.
Unclassified share: 100% of the O recursive-call and exclusive-time attribution for this phase.
Remaining uncertainty: a READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

## MPRWE round 2 (READY3.1)

The non-identity A3 matched probe used 10 calls, 0.058 ms comparison-exclusive and 0.001 ms reduction-exclusive (0.060 ms wall).

### B. Original provenance

Root 1633 has complete aggregate coverage: 3,180,470 calls and 21,549.825 ms comparison-exclusive time. A selected raw rerun captured 4,124 traced calls and 10,000 raw events; representative M1 nodes include `DerivedCategory.isRightDerivedFunctor_internalHomQhObj_comp_tensorLeft`, `DerivedCategory.tensorLeftQhObjCounit`, `EquivLike.coe`, and `HomotopyCategory.tensorHomAdjunction`.

| Category | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.146 | 0.001% |
| M1 | 2,390,795 | 21,498.522 | 99.762% |
| M2 | 22 | 0.295 | 0.001% |
| Matched | 789,652 | 50.862 | 0.236% |
| Unclassified | 0 | 0.000 | 0.000% |

### C. Intervention and restoration

`O1-hv-aligned` changes the root; the aligned control completes in 2 calls / 0.141 ms comparison-exclusive. It is invalid as selective C. The supplied restoration is a 2-call / 0.206 ms comparison control and does not reproduce O.

### 9. Outcome

**Outcome C (M1 propagation).** 99.762% of original exclusive time is M1 and M2 is negligible. READY3.1 resolves the former provenance uncertainty without relying on the invalid whole-root ablation.

