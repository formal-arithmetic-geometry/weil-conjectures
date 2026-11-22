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

