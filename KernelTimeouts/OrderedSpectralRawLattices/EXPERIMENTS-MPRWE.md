# Mismatch Provenance and Recursive Workload Report

Case: OrderedSpectralRawLattices
Lean / Mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; READY2-4.35.0.
Instrumentation: observational READY2 counters and capped path trace; no READY3 provenance build was available during this run.

## 1. Root mismatch

Root conversion: final conversion from exists_stratified_lisse_integral_lattice to RawStratifiedLattices.
Exact pair summary: competing regular/Henselian/domain instance routes; dominant path Exists -> Quiver.Hom -> Functor.obj
The root mismatch is M0 by the plan's operational definition. This report does not revisit the established trigger or unfolding choice.

## 2. Matched baseline

Baseline level: A3 diagnostic. The matched probe uses a smaller operation or component obligation and does not preserve the full dependent consumer.

| Probe | Measured result |
|---|---|
| O | 51.962 s / 18,944,709 calls; comparison 51.938 s; reduction 0.024 s; depth 71 |
| M | 0.702 ms / 83 calls; comparison 0.326 ms; reduction 0.376 ms; depth 17 |
| A | no root over 100 ms after all three routes are aligned |
| R | 36.145 s / 18,944,728 calls in fresh restored-domain replay; earlier partial restores 35.939-36.282 s |

The fresh M probe typechecked with full Kernel checking and performed a non-identity conversion. It is not A0/A1. The exact source pair and audit are in probes/mprwe/{Matched,Original,Aligned,Restored}.lean.

## 3. Provenance distribution

READY2 records recursive counts, branch/depth histograms, inclusive path samples, and root timers, but not parent-child IDs, reduction predecessors, local-context fingerprints, or semantic first divergences. Exclusive provenance attribution is therefore intentionally Unclassified.

| Provenance | Recursive calls | Exclusive comparison time | Status |
|---|---:|---:|---|
| M0 | not separable | not separable | root entry identified |
| M1 | not separable | not separable | M0 is the R/H/D route bundle. Nested Exists/Quiver.Hom descendants may inherit M0, but no pair-context identity or reduction predecessor is recorded. |
| M2 | not separable | not separable | no reduction event recorded |
| Matched descendants | not separable | not separable | no context-aware pair identity |
| Unclassified | all O calls | all O comparison time | measured remainder |

Root partitions are not summed with inclusive child path samples. Trace path labels are qualitative and do not constitute exclusive attribution.

## 4. Newly exposed divergences

No major M2 can be established at call-node granularity with READY2. M0 is the R/H/D route bundle. Nested Exists/Quiver.Hom descendants may inherit M0, but no pair-context identity or reduction predecessor is recorded. The reduction that immediately preceded a candidate M2, its call ID, and its descendant fan-out are unavailable. Orthogonal dependent/proposition tags are available only as overlapping aggregate timers in inherited AD/IM records.

## 5. Selective descendant alignment

O1/O2/O3 restore individual routes and remain expensive; all-route alignment removes the root but aligns M0 and is invalid for C. No valid O12/O-all control.

Every copied source snapshot is under probes/mprwe/; none modifies the library.

## 6. Conclusion

Outcome E: complete bundle causality is measured, individual provenance is not. Cheap object-map M does not establish intrinsic cost for the full root.

Matched intrinsic cost: only the A3 diagnostic cost is measured; it must not be generalized to O.
Inherited M1 cost: plausible in the dependent paths above, but quantitatively unclassified.
Newly exposed M2 cost: unclassified; no causal M2 intervention is valid.
Unclassified share: 100% of the O recursive-call and exclusive-time attribution for this phase.
Remaining uncertainty: a READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

