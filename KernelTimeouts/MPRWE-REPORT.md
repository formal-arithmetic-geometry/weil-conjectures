# KernelTimeouts MPRWE cross-case synthesis

## MPRWE round 4 (READY3.2 only)

Analyzer: READY3.2 `mprwe_analyze.py`, with process-wide atomic root identity
and active-root pinning. Counter O and analyzed trace roots agree on calls for
every valid case. Trace aggregate exclusive time includes the trace hash/path
overhead; raw coverage is the bounded enter/exit capture. Older round-2/3
tables are superseded by this table.

Shares are ordered M0 / M1 / M2 / Matched / Unclassified. `O/analyzed` is the
counter-root call count / analyzed-root call count.

| Case | O/analyzed calls | Counter / trace ms | Raw coverage | Call shares (%) | Exclusive-time shares (%) | C result | Outcome |
|---|---:|---:|---:|---|---|---|---|
| Derived-Completion Cone | 12,220,823 / 12,220,823 | 82,320.997 / 84,401.270 | 1,562 / 12,220,823 (0.013%) | 0.000 / 76.560 / 0.074 / 23.366 / 0.000 | 0.000 / 99.725 / 0.064 / 0.210 / 0.000 | dependent-field alignment changes the root telescope; restoration is diagnostic | D |
| FiniteBaseChange | 239,340,712 / 239,340,712 | 681,687.160 / 1,082,179.217 | 3,828 / 239,340,712 (0.002%) | 0.000 / 54.398 / 16.920 / 28.682 / 0.000 | 0.000 / 74.113 / 24.473 / 1.414 / 0.000 | descendant alignment changes root; restoration diagnostic | D |
| IntegralComparison | 9,426,198 / 9,426,198 | 83,768.275 / 224,445.716 | 3,913 / 9,426,198 (0.042%) | 0.000 / 70.875 / 0.267 / 28.857 / 0.000 | 0.000 / 99.839 / 0.052 / 0.109 / 0.000 | After changes root; Before restores O | C |
| RealPurity | 17,310,168 / 17,310,168 | 52,925.953 / 85,908.939 | 3,222 / 17,310,168 (0.019%) | 0.000 / 46.148 / 25.171 / 28.681 / 0.000 | 0.000 / 63.672 / 35.139 / 1.189 / 0.000 | dependent witness telescope changes | D |
| OrderedSpectralRawLattices | 18,944,709 / 18,944,709 | 35,362.863 / 65,054.912 | 4,333 / 18,944,709 (0.023%) | 0.000 / 43.922 / 18.473 / 37.605 / 0.000 | 0.000 / 62.919 / 36.382 / 0.698 / 0.000 | route controls change dependent root | D |
| EtaleHom | 3,180,470 / 3,180,470 | 22,573.922 / 26,975.321 | 4,124 / 3,180,470 (0.130%) | 0.000 / 75.171 / 0.001 / 24.828 / 0.000 | 0.001 / 99.800 / 0.002 / 0.197 / 0.000 | hv alignment changes root; no M0-preserving control | C |
| F66Adj | 3,897,905 / 3,897,905 | 26,603.785 / 30,149.979 | 3,685 / 3,897,905 (0.095%) | 0.000 / 75.968 / 0.000 / 24.032 / 0.000 | 0.000 / 99.791 / 0.000 / 0.209 / 0.000 | hR/Over telescope changes root | C |
| ImageHomCounit | 6,359,958 / 6,359,958 | 42,138.453 / 42,672.620 | 3,773 / 6,359,958 (0.059%) | 0.000 / 75.178 / 0.004 / 24.818 / 0.000 | 0.001 / 99.761 / 0.009 / 0.230 / 0.000 | endpoint alignment changes root | C |
| RealPushforward | 17,340,236 / 17,340,236 | 125,356.436 / 105,827.556 | 3,122 / 17,340,236 (0.018%) | 0.000 / 46.148 / 25.171 / 28.680 / 0.000 | 0.000 / 63.011 / 35.985 / 1.003 / 0.000 | polynomial alignment changes dependent consumer | D |

## §11 answer

The workload is mixed. Inherited M1 propagation dominates Cone, IntegralComparison,
EtaleHom, F66Adj, and ImageHomCounit, while FiniteBaseChange, RealPurity,
OrderedSpectralRawLattices, and RealPushforward expose material M2 time. The
Cone is also M1-dominated after correcting the stale diagnostic root. Matched
descendants are measurable but not time-dominant. All attempted selective
alignments alter the dependent root or its M0 telescope; restored variants are
diagnostic restorations rather than causal controls. Branch round4 base:
`dataset/kernel-timeouts`.
