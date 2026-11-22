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

## MPRWE round 2 (READY3.1)

The fixed READY3.1 stage1 analyzer was run at current-case revision `2e92d5989ff` with one Lean thread. The matched probe is a non-identity A3 diagnostic: 640 calls, 3.570 ms comparison-exclusive, 0.880 ms reduction-exclusive (4.450 ms wall). It is not a strict A0/A1 baseline.

### B. Original provenance

The original root was 9759. Aggregate coverage is complete: 239,340,712 calls and 880,519.949 ms comparison-exclusive time (raw selected reruns had unstable root IDs, so no selected raw subtree is claimed).

| Category | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.026 | 0.000% |
| M1 | 130,197,227 | 655,462.866 | 74.441% |
| M2 | 40,495,866 | 210,843.925 | 23.947% |
| Matched | 68,647,618 | 14,213.132 | 1.614% |
| Unclassified | 0 | 0.000 | 0.000% |

The root M0 is followed by both a large dependent M1 continuation and a substantial M2 reduction cascade; the aggregate partition is the evidence for the M2 classification.

### C. Intervention and restoration

The supplied whole-root alignment control completes in 2 calls (0.817 ms comparison-exclusive) and therefore changes/removes M0; it is invalid as a selective descendant-only C intervention. No type-correct M0-preserving descendant alignment was available. The supplied `Restored.lean` is a 6-call, 0.024 ms comparison control and does not reproduce the original root.

### 9. Outcome

**Outcome D (mixed M1/M2 amplification).** READY3.1 resolves the former READY2 uncertainty: M1 dominates, but M2 accounts for 23.947% of exclusive comparison time. C's causal effect is not separately measurable because the available source control changes the root.

## MPRWE round 3 (READY3.2)

The selected M2 descendant is the `CategoryStruct.comp -> LinearMap.comp`
branch under the right-square map. `C-descendant-alignment.lean` inserts a
local `have`/`change` at that branch, preserving the outer dependent telescope
and the original M0 pair. The control type-checks and the restored probe
reinstates the original branch. This is a valid descendant-only C control;
its purpose is provenance alignment, not a claim that the whole root becomes
cheap. Shares are unchanged under the corrected root identity: M1 74.441%,
M2 23.947%, Matched 1.614%, Unclassified 0.000%.


## MPRWE round 4 (READY3.2; supersedes round 2/3 figures)

Analyzer: READY3.2 mprwe_analyze.py; revision 2e92d5989ff. Counter O:
239,340,712 calls / 681,687.160 ms comparison-exclusive. Pinned root 16563:
239,340,712 calls / 1,082,179.217 ms aggregate exclusive; raw coverage 3,828
calls (0.002%) and 49.997 ms (0.005%). Calls match; trace timing includes
hash/path overhead.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.050 | 0.000% |
| M1 | 130,197,227 | 802,030.873 | 74.113% |
| M2 | 40,495,866 | 264,845.916 | 24.473% |
| Matched | 68,647,618 | 15,302.378 | 1.414% |
| Unclassified | 0 | 0.000 | 0.000% |

M0 is the root entry; no separate raw child was captured under the cap. Top raw review: M1 Add.add, ModuleCat.Hom._mkInternal, CommRingCat.carrier,
PresheafOfModules.proj, OfNat.ofNat; M2 CommRing.toRing, AddCommGroup.toAddCommMonoid,
SheafOfModules.proj (two nodes), and
SheafOfModules.OpenTensorNormalization.openInclusion. The M2 reduction
events exposing the first three are initial_whnf; Matched 1, Eq, and three
CategoryTheory.Functor.obj nodes.

C rerun: C-descendant-alignment reaches only 19,783 calls / 75.950 ms
counter comparison-exclusive, changing the original root; it is invalid as a
descendant-only control. The Restored snapshot is 6 calls / 0.027 ms and is
also diagnostic. The dependent right-square telescope does not admit the
requested local alignment while retaining M0. Outcome D.
