# Mismatch Provenance and Recursive Workload Report

Case: IntegralComparisonPullbackRealizationShifts
Lean / Mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; READY2-4.35.0.
Instrumentation: observational READY2 counters and capped path trace; no READY3 provenance build was available during this run.

## 1. Root mismatch

Root conversion: downstream change conversion after commShift_of_localization and intro P m.
Exact pair summary: M.realization.hom.app (DerivedCategory.Q.obj P) >> one versus beta-expanded Q.obj input; path CategoryStruct.comp -> NatTrans.app
The root mismatch is M0 by the plan's operational definition. This report does not revisit the established trigger or unfolding choice.

## 2. Matched baseline

Baseline level: A3 diagnostic. The matched probe uses a smaller operation or component obligation and does not preserve the full dependent consumer.

| Probe | Measured result |
|---|---|
| O | 73.839 s / 9,426,253 calls; comparison 44.816 s; reduction 29.024 s; depth 183 |
| M | 0.729 ms / 54 calls (diagnostic) |
| A | first-instance alignment remains expensive: 88.99 s diagnostic; no removal of downstream root |
| R | 73.107 s / 9,426,253 calls |

The fresh M probe typechecked with full Kernel checking and performed a non-identity conversion. It is not A0/A1. The exact source pair and audit are in probes/mprwe/{Matched,Original,Aligned,Restored}.lean.

## 3. Provenance distribution

READY2 records recursive counts, branch/depth histograms, inclusive path samples, and root timers, but not parent-child IDs, reduction predecessors, local-context fingerprints, or semantic first divergences. Exclusive provenance attribution is therefore intentionally Unclassified.

| Provenance | Recursive calls | Exclusive comparison time | Status |
|---|---:|---:|---|
| M0 | not separable | not separable | root entry identified |
| M1 | not separable | not separable | M0 is the first endpoint/provider divergence. The nested NatTrans.app subtree is an inferred M1/M2 candidate, but no reduction event or pair identity permits a reliable label. |
| M2 | not separable | not separable | no reduction event recorded |
| Matched descendants | not separable | not separable | no context-aware pair identity |
| Unclassified | all O calls | all O comparison time | measured remainder |

Root partitions are not summed with inclusive child path samples. Trace path labels are qualitative and do not constitute exclusive attribution.

## 4. Newly exposed divergences

No major M2 can be established at call-node granularity with READY2. M0 is the first endpoint/provider divergence. The nested NatTrans.app subtree is an inferred M1/M2 candidate, but no reduction event or pair identity permits a reliable label. The reduction that immediately preceded a candidate M2, its call ID, and its descendant fan-out are unavailable. Orthogonal dependent/proposition tags are available only as overlapping aggregate timers in inherited AD/IM records.

## 5. Selective descendant alignment

O1-prefix-aligned is a negative partial alignment (trace root 88.313 s). It changes the first visible divergence while the downstream root remains, so it is invalid as strict M0-preserving intervention. R restores the original scale.

Every copied source snapshot is under probes/mprwe/; none modifies the library.

## 6. Conclusion

Outcome E: the first leaf is not sufficient; the expensive downstream comparison remains. Provenance proportions are unclassified.

Matched intrinsic cost: only the A3 diagnostic cost is measured; it must not be generalized to O.
Inherited M1 cost: plausible in the dependent paths above, but quantitatively unclassified.
Newly exposed M2 cost: unclassified; no causal M2 intervention is valid.
Unclassified share: 100% of the O recursive-call and exclusive-time attribution for this phase.
Remaining uncertainty: a READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

