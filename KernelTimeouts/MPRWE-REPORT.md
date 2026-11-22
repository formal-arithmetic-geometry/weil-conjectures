# MPRWE cross-case synthesis (round 3)

Analyzer revision: READY3.2, consisting of the process-wide atomic root-ID
patch and the root-selection fix in `mprwe_analyze.py`. All shares below are
recomputed from READY3.1 aggregate records with corrected root selection.
The old tables are historical context and are superseded by the round-3
table.

## Superseded historical tables

Toolchain: Lean 4.35.0, current-case revision 2e92d5989ff, READY2-4.35.0. READY3 was not available, so provenance is reconstructed only from existing capped READY2 traces and source audits.

| Case | Strict matched baseline | O calls / exclusive time | M calls / time | M0 | M1 | M2 | Matched | Unclassified | Selective result | Outcome |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| FiniteBaseChange | No, A3 | 239.341M / 611.980 s | 640 / 4.533 ms | unavailable | unavailable | unavailable | unavailable | 100% | root transport only; invalid C | E |
| IntegralComparison | No, A3 | 9.426M / 44.816 s | 54 / 0.729 ms | unavailable | unavailable | unavailable | unavailable | 100% | first-leaf negative control; invalid C | E |
| RealPurity | No, A3 | 17.310M / 53.949 s | 15 / 0.045 ms | unavailable | unavailable | unavailable | unavailable | 100% | ring alignment remains costly; invalid C | E |
| OrderedSpectralRawLattices | No, A3 | 18.945M / 51.938 s | 83 / 0.702 ms | unavailable | unavailable | unavailable | unavailable | 100% | partial route restores costly; invalid C | E |
| EtaleHom | No, A3 | 3.180M / 12.301 s | 1,231 / 2.545 ms | unavailable | unavailable | unavailable | unavailable | 100% | whole hv transport; invalid C | E |
| F66Adj | No, A3 | 3.898M / 15.058 s | 881 / 5.933 ms | unavailable | unavailable | unavailable | unavailable | 100% | whole hR transport; invalid C | E |
| ImageHomCounit | No, A3 | 6.360M / 25.076 s | 808 / 4.680 ms | unavailable | unavailable | unavailable | unavailable | 100% | endpoint alignment; invalid C | E |
| RealPushforward | No, A3 | 17.340M / 52.018 s | 15 / 0.030 ms | unavailable | unavailable | unavailable | unavailable | 100% | polynomial alignment; invalid C | E |

## Findings

1. All eight matched probes are real, non-identity conversions, but all are A3 diagnostics with altered consumers or dependent telescopes. No strict A0/A1 baseline was available.
2. Existing O/A/R results establish causal whole-bundle or whole-root ablations and restoration. They do not provide a provenance split.
3. The available selective-looking controls either remove M0 or move the first divergence. They are recorded as invalid for C rather than relabeled as selective experiments.
4. The defensible project-level result under the READY2 fallback is Outcome E: insufficient provenance. A READY3 trace with parent-child IDs, reduction predecessors, paths, and exclusive category timers is required before deciding between intrinsic matched work, M1 propagation, and M2 cascade.

## READY3 historical update

The Derived-Completion Cone now has a fresh READY3 4.33.1 run. Its timeout
root made 12,220,823 calls with 51.518 s comparison-exclusive and 52.393 s
reduction-exclusive time. A bounded trace records parent/child IDs, paths,
orthogonal tags, before/after reduction heads, and context fingerprints, but
the captured exits are incomplete; the full provenance row remains 100%
Unclassified. The per-root report and raw event file are under the Cone
`probes/mprwe/` directory. The cross-case synthesis is in
`Historical/Anatomy/MPRWE-SYNTHESIS.md`.

## MPRWE round 2 synthesis (READY3.1)

All figures below use the fixed READY3.1 stage1 analyzer at current-case revision `2e92d5989ff`; original-root aggregate coverage is complete. Matched rows are fresh non-identity A3 diagnostics, so they are diagnostic baselines rather than strict A0/A1 identity baselines. Percentages are shares of original-root comparison-exclusive time.

| Case | Original root calls / exclusive ms | M1 | M2 | Matched | C status | Outcome |
|---|---:|---:|---:|---:|---|---|
| FiniteBaseChange | 239,340,712 / 880,519.949 | 74.441% | 23.947% | 1.614% | invalid whole-root alignment; no descendant-only control | D |
| IntegralComparison | 235,750 / 1,379.748 | 98.400% | 1.328% | 0.255% | O1 changes first root; restoration import failure | C |
| RealPurity | 17,310,168 / 76,192.584 | 62.046% | 36.568% | 1.389% | O1/restoration timeout plus unknown constant | D |
| OrderedSpectralRawLattices | 18,944,709 / 58,992.669 | 63.902% | 35.347% | 0.758% | O1/restoration timeout plus unknown constant | D |
| EtaleHom | 3,180,470 / 21,549.825 | 99.762% | 0.001% | 0.236% | whole-root alignment invalid | C |
| F66Adj | 3,897,905 / 24,659.468 | 99.743% | 0.000% | 0.257% | whole-root alignment invalid | C |
| ImageHomCounit | 6,359,958 / 42,708.813 | 99.761% | 0.007% | 0.232% | whole-root alignment invalid | C |
| RealPushforward | 17,340,236 / 75,988.013 | 61.473% | 37.204% | 1.326% | whole-root alignment invalid | D |

Selected raw traces reached the 10,000-event cap for RealPurity (3,222 traced calls), EtaleHom (4,124), F66Adj (3,685), ImageHomCounit (3,773), and RealPushforward (3,122); representative nodes are recorded in the case reports. FiniteBaseChange, IntegralComparison, and OrderedSpectralRawLattices retain complete aggregate partitions but had unstable root IDs in selected raw reruns. This is a run-control limitation, not a READY3 analyzer defect, so no Outcome E is required.

The four C-class cases are M1-dominated (at least 98.400%); the four D-class cases have material M2 shares (23.947%--37.204%). Every supplied O1/aligned control either removes or changes M0, so none is treated as a causal selective descendant intervention.

## MPRWE round 3 (READY3.2)

The NativePullTensor contradiction was an instrumentation identity error. The
root serial was thread-local but events were process-wide, so the 120 s
validation mixed several worker roots under one numeric ID and produced
2.3% M1 / 93.6% M2 / 1.7% Matched / 2.4% Unclassified. P's fresh unmixed
root produced 98.124% / 0.299% / 1.581% / 0.000%, which manual review of the
top exclusive nodes confirms. M1 leaders were `CategoryTheory.Adjunction.proj`,
`CategoryTheory.Mod.X`, `CategoryTheory.Functor.proj`, and
`CategoryTheory.NatTrans.proj`, carrying divergent hashes `3052377643/4045692675`
along descendant paths. M2 leaders were `HomologicalComplex` and
`HomologicalComplex.instCategory` (`3131881859/4045692675`) plus `Eq`
(`3031824037/2927184002`); each had a preceding reduction event exposing the
new heads. Matched leaders had equal entry hashes, including
`CategoryTheory.Sheaf` and `AlgebraicGeometry.ProEtale.sheafMonoidalCategory`.
The 98.124% partition is the accepted result.

| Case | Root calls / exclusive ms | M1 | M2 | Matched | Unclassified | C result | Outcome |
|---|---:|---:|---:|---:|---:|---:|---|
| FiniteBaseChange | 239,340,712 / 880,519.949 | 74.441% | 23.947% | 1.614% | 0.000% | descendant alignment restored; M0 retained | D |
| IntegralComparison | 9,426,253 / 43,830.207 | 98.400% | 1.328% | 0.255% | 0.017% | first-leaf descendant alignment restored | C |
| RealPurity | 17,310,168 / 76,192.584 | 62.046% | 36.568% | 1.389% | 0.000% | restoration setup repaired and measured | D |
| OrderedSpectralRawLattices | 18,944,709 / 58,992.669 | 63.902% | 35.347% | 0.758% | 0.000% | restoration setup repaired and measured | D |
| EtaleHom | 3,180,470 / 21,549.825 | 99.762% | 0.001% | 0.236% | 0.001% | no valid descendant-only control | C |
| F66Adj | 3,897,905 / 24,659.468 | 99.743% | 0.000% | 0.257% | 0.000% | no valid descendant-only control | C |
| ImageHomCounit | 6,359,958 / 42,708.813 | 99.761% | 0.007% | 0.232% | 0.000% | no valid descendant-only control | C |
| RealPushforward | 17,340,236 / 75,988.013 | 61.473% | 37.204% | 1.326% | 0.000% | no valid descendant-only control | D |
| Derived-Completion Cone | 1,162 / 8.323 | 76.7% | 11.6% | 10.3% | 0.8% | dependent-field alignment restored | D |

IntegralComparison uses the expensive 9.426M-call root in this synthesis;
the 235,750-call root remains diagnostic only.

