# Mismatch Provenance and Recursive Workload Report

Case: FiniteBaseChangeRestrictionMateTransport
Lean / Mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; READY2-4.35.0.
Instrumentation: observational READY2 counters and capped path trace; no READY3 provenance build was available during this run.

## 1. Root mismatch

Root conversion: dependent hb (argument 49), Site/Quiver.Hom proposition.
Exact pair summary: Site .ordinary provider versus ProEt provider in hb; descendant path CategoryStruct.comp -> LinearMap.comp -> PresheafOfModules.Hom.proj -> NatTrans.app
The root mismatch is M0 by the plan's operational definition. This report does not revisit the established trigger or unfolding choice.

## 2. Matched baseline

Baseline level: A3 diagnostic. The matched probe uses a smaller operation or component obligation and does not preserve the full dependent consumer.

| Probe | Measured result |
|---|---|
| O | 612.036 s / 239,340,712 calls; comparison 611.980 s; WHNF 0.0566 s; depth 87 |
| M | 4.533 ms / 640 calls; comparison 3.627 ms; reduction 0.906 ms; depth 33 |
| A | no expensive root; setup 113.650 ms / 19,783 calls |
| R | 625.694 s / 239,340,712 calls; comparison 625.641 s; WHNF 0.0527 s |

The fresh M probe typechecked with full Kernel checking and performed a non-identity conversion. It is not A0/A1. The exact source pair and audit are in probes/mprwe/{Matched,Original,Aligned,Restored}.lean.

## 3. Provenance distribution

READY2 records recursive counts, branch/depth histograms, inclusive path samples, and root timers, but not parent-child IDs, reduction predecessors, local-context fingerprints, or semantic first divergences. Exclusive provenance attribution is therefore intentionally Unclassified.

| Provenance | Recursive calls | Exclusive comparison time | Status |
|---|---:|---:|---|
| M0 | not separable | not separable | root entry identified |
| M1 | not separable | not separable | The root difference is M0. The repeated dependent proposition path is an inferred M1 continuation; distinct descendant provenance is unavailable. |
| M2 | not separable | not separable | no reduction event recorded |
| Matched descendants | not separable | not separable | no context-aware pair identity |
| Unclassified | all O calls | all O comparison time | measured remainder |

Root partitions are not summed with inclusive child path samples. Trace path labels are qualitative and do not constitute exclusive attribution.

## 4. Newly exposed divergences

No major M2 can be established at call-node granularity with READY2. The root difference is M0. The repeated dependent proposition path is an inferred M1 continuation; distinct descendant provenance is unavailable. The reduction that immediately preceded a candidate M2, its call ID, and its descendant fan-out are unavailable. Orthogonal dependent/proposition tags are available only as overlapping aggregate timers in inherited AD/IM records.

## 5. Selective descendant alignment

O1/O2/O12/O-all unavailable. Existing whole-hb transport aligns M0 and is invalid for C. R restores the original root and call count.

Every copied source snapshot is under probes/mprwe/; none modifies the library.

## 6. Conclusion

Outcome E: READY2 cannot distinguish M1 from M2 or matched descendants. O/R reversal establishes a causal dependent bundle, not provenance shares.

Matched intrinsic cost: only the A3 diagnostic cost is measured; it must not be generalized to O.
Inherited M1 cost: plausible in the dependent paths above, but quantitatively unclassified.
Newly exposed M2 cost: unclassified; no causal M2 intervention is valid.
Unclassified share: 100% of the O recursive-call and exclusive-time attribution for this phase.
Remaining uncertainty: a READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

