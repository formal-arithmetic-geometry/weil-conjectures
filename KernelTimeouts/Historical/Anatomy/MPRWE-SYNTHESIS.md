# MPRWE Cross-case Synthesis (round 4)

Analyzer revision: READY3.2 `mprwe_analyze.py`. The instrumented kernels use
process-wide atomic root identity and active-root pinning. Every valid trace
root below matches the independent READY3.2 counter root in total calls;
counter / trace times are comparison-exclusive milliseconds. Trace aggregate
time includes hash/path bookkeeping. Raw coverage is the bounded enter/exit
capture. Older synthesis tables are superseded.

Shares are ordered M0 / M1 / M2 / Matched / Unclassified. The call-share and
exclusive-time-share columns are both included because the two partitions are
not interchangeable.

Round-5 outcome rule, applied uniformly: a valid root is **C** when its
exclusive-time M2 share is below 5% and its Matched share is below 2%, provided
there is no valid M0-preserving C control showing mixed amplification. It is
**D** when either share reaches its threshold, or when such a valid C control
shows the mixed workload. Root-changing or type-invalid alignments do not by
themselves change C to D.

| Case | O/analyzed calls | Counter / trace ms | Raw coverage | Call shares (%) | Exclusive-time shares (%) | C result | Outcome |
|---|---:|---:|---:|---|---|---|---|
| Derived-Completion Cone | 12,220,823 / 12,220,823 | 82,320.997 / 84,401.270 | 1,562 / 12,220,823 (0.013%) | 0.000 / 76.560 / 0.074 / 23.366 / 0.000 | 0.000 / 99.725 / 0.064 / 0.210 / 0.000 | dependent-field alignment changes root telescope; restoration diagnostic | C |
| FiniteBaseChange | 239,340,712 / 239,340,712 | 681,687.160 / 1,082,179.217 | 3,828 / 239,340,712 (0.002%) | 0.000 / 54.398 / 16.920 / 28.682 / 0.000 | 0.000 / 74.113 / 24.473 / 1.414 / 0.000 | descendant alignment changes root; restoration diagnostic | D |
| IntegralComparison | 9,426,198 / 9,426,198 | 83,768.275 / 224,445.716 | 3,913 / 9,426,198 (0.042%) | 0.000 / 70.875 / 0.267 / 28.857 / 0.000 | 0.000 / 99.839 / 0.052 / 0.109 / 0.000 | After changes root; Before restores O | C |
| RealPurity | 17,310,168 / 17,310,168 | 52,925.953 / 85,908.939 | 3,222 / 17,310,168 (0.019%) | 0.000 / 46.148 / 25.171 / 28.681 / 0.000 | 0.000 / 63.672 / 35.139 / 1.189 / 0.000 | dependent witness telescope changes | D |
| OrderedSpectralRawLattices | 18,944,709 / 18,944,709 | 35,362.863 / 65,054.912 | 4,333 / 18,944,709 (0.023%) | 0.000 / 43.922 / 18.473 / 37.605 / 0.000 | 0.000 / 62.919 / 36.382 / 0.698 / 0.000 | route controls change dependent root | D |
| EtaleHom | 3,180,470 / 3,180,470 | 22,573.922 / 26,975.321 | 4,124 / 3,180,470 (0.130%) | 0.000 / 75.171 / 0.001 / 24.828 / 0.000 | 0.001 / 99.800 / 0.002 / 0.197 / 0.000 | hv alignment changes root; no M0-preserving control | C |
| F66Adj | 3,897,905 / 3,897,905 | 26,603.785 / 30,149.979 | 3,685 / 3,897,905 (0.095%) | 0.000 / 75.968 / 0.000 / 24.032 / 0.000 | 0.000 / 99.791 / 0.000 / 0.209 / 0.000 | hR/Over telescope changes root | C |
| ImageHomCounit | 6,359,958 / 6,359,958 | 42,138.453 / 42,672.620 | 3,773 / 6,359,958 (0.059%) | 0.000 / 75.178 / 0.004 / 24.818 / 0.000 | 0.001 / 99.761 / 0.009 / 0.230 / 0.000 | endpoint alignment changes root | C |
| RealPushforward | 17,340,236 / 17,340,236 | 125,356.436 / 105,827.556 | 3,122 / 17,340,236 (0.018%) | 0.000 / 46.148 / 25.171 / 28.680 / 0.000 | 0.000 / 63.011 / 35.985 / 1.003 / 0.000 | polynomial alignment changes dependent consumer | D |
| NativePullTensor | 2,685,580 / 2,685,580 | 16,554.296 / 20,949.497 | 0 / 2,685,580 (0.000%) | 0.000 / 41.730 / 0.448 / 57.822 / 0.000 | 0.000 / 98.126 / 0.302 / 1.569 / 0.000 | provider alignment changes root; no descendant-only control | C |
| PR1556 | 6,670,198 / 6,670,198 | 29,691.693 / 53,056.120 | 179,920 / 6,670,198 (2.697%) | 0.000 / 75.051 / 0.137 / 24.812 / 0.000 | 0.000 / 99.622 / 0.072 / 0.306 / 0.000 | major-premise alignment changes root and removes M0 | C |
| PR1625 | 11,757,788 / 11,757,788 | 48,799.297 / 76,455.101 | 186,547 / 11,757,788 (1.586%) | 0.000 / 68.984 / 0.040 / 30.976 / 0.000 | 0.001 / 99.406 / 0.068 / 0.525 / 0.001 | outer-major alignment changes root and removes M0 | C |
| PR1563 | 2,563,145 / 2,563,145 | 10,590.442 / 28,045.607 | 180,953 / 2,563,145 (7.061%) | 0.000 / 75.084 / 0.040 / 24.876 / 0.000 | 0.000 / 99.553 / 0.043 / 0.405 / 0.000 | provider alignment changes dependent root | C |
| PR1624 | 6,598,545 / 6,598,545 | 25,760.364 / 40,168.150 | 1,483 / 6,598,545 (0.022%) | 0.000 / 79.035 / 0.004 / 20.961 / 0.000 | 0.000 / 99.804 / 0.007 / 0.188 / 0.001 | broad alignment changes root to 456,393 calls; no M0-preserving child control; identical restoration | C |
| PR1627 | 10,904,899 / 10,904,899 | 22,866.272 / 30,919.746 | 187,782 / 10,904,899 (1.722%) | 0.000 / 24.021 / 13.871 / 62.107 / 0.000 | 0.000 / 66.712 / 22.789 / 10.495 / 0.000 | aligned/restored preserve root; M2 shares 25.1% / 26.1% and do not fall | D |
| PR2122 | 2,257,184 / 2,257,184 | 13,239.259 / 16,827.104 | 177,324 / 2,257,184 (7.856%) | 0.000 / 79.648 / 2.298 / 18.005 / 0.050 | 0.000 / 97.397 / 2.177 / 0.360 / 0.065 | recursor alignment changes dependent root | C |

## §11 answer

The workload is mixed across cases. Under the rule above, C is assigned to
Cone, IntegralComparison, EtaleHom, F66Adj, ImageHomCounit, NativePullTensor,
PR1556, PR1625, PR1563, PR1624, and PR2122: each has M2 below 5% and Matched
below 2%, with no valid root-preserving C amplification. D is assigned to
FiniteBaseChange, RealPurity, OrderedSpectralRawLattices, RealPushforward, and
PR1627 because M2 is at least 5% (and PR1627 also has Matched above 2%).
PR1627's aligned/restored controls preserve its root but do not reduce M2.
PR1624 now reaches its expensive root; the prior E was a stale or unavailable
instrumented-binary setup issue, and its broad alignment is an invalid
root-changing C attempt. Branch heads are recorded in the two dataset reports.
