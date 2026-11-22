# MPRWE cross-case synthesis

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

