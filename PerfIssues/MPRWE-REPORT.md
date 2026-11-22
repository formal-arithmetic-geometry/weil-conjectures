# PerfIssues MPRWE cross-case synthesis

## MPRWE round 4 (READY3.2 only)

Analyzer: READY3.2 `mprwe_analyze.py`, with process-wide atomic root identity
and active-root pinning. Counter O and analyzed trace roots agree on calls for
each valid case. Trace aggregate exclusive time includes trace hash/path
overhead. Older round-2/3 tables are superseded by this table.

Shares are ordered M0 / M1 / M2 / Matched / Unclassified.

Round-5 outcome rule: classify a valid root as C when exclusive-time M2 is
below 5% and Matched is below 2%, unless a valid M0-preserving C control shows
mixed amplification. Classify it as D when either share reaches its threshold
or that valid C control shows mixed amplification. Root-changing or invalid
alignments do not by themselves change C to D.

| Case | O/analyzed calls | Counter / trace ms | Raw coverage | Call shares (%) | Exclusive-time shares (%) | C result | Outcome |
|---|---:|---:|---:|---|---|---|---|
| NativePullTensor | 2,685,580 / 2,685,580 | 16,554.296 / 20,949.497 | 0 / 2,685,580 (0.000%) | 0.000 / 41.730 / 0.448 / 57.822 / 0.000 | 0.000 / 98.126 / 0.302 / 1.569 / 0.000 | provider alignment changes root; no descendant-only control | C |
| PR1556 | 6,670,198 / 6,670,198 | 29,691.693 / 53,056.120 | 179,920 / 6,670,198 (2.697%) | 0.000 / 75.051 / 0.137 / 24.812 / 0.000 | 0.000 / 99.622 / 0.072 / 0.306 / 0.000 | major-premise alignment changes root and removes M0 | C |
| PR1625 | 11,757,788 / 11,757,788 | 48,799.297 / 76,455.101 | 186,547 / 11,757,788 (1.586%) | 0.000 / 68.984 / 0.040 / 30.976 / 0.000 | 0.001 / 99.406 / 0.068 / 0.525 / 0.001 | outer-major alignment changes root and removes M0 | C |
| PR1563 | 2,563,145 / 2,563,145 | 10,590.442 / 28,045.607 | 180,953 / 2,563,145 (7.061%) | 0.000 / 75.084 / 0.040 / 24.876 / 0.000 | 0.000 / 99.553 / 0.043 / 0.405 / 0.000 | provider alignment changes dependent root | C |
| PR1624 | 6,598,545 / 6,598,545 | 25,760.364 / 40,168.150 | 1,483 / 6,598,545 (0.022%) | 0.000 / 79.035 / 0.004 / 20.961 / 0.000 | 0.000 / 99.804 / 0.007 / 0.188 / 0.001 | broad alignment changes root to 456,393 calls; no M0-preserving child control; identical restoration | C |
| PR1627 | 10,904,899 / 10,904,899 | 22,866.272 / 30,919.746 | 187,782 / 10,904,899 (1.722%) | 0.000 / 24.021 / 13.871 / 62.107 / 0.000 | 0.000 / 66.712 / 22.789 / 10.495 / 0.000 | aligned/restored preserve root; M2 shares 25.1% / 26.1% and do not fall | D |
| PR2122 | 2,257,184 / 2,257,184 | 13,239.259 / 16,827.104 | 177,324 / 2,257,184 (7.856%) | 0.000 / 79.648 / 2.298 / 18.005 / 0.050 | 0.000 / 97.397 / 2.177 / 0.360 / 0.065 | recursor alignment changes dependent root | C |

Under the uniform round-5 rule, NativePullTensor, PR1556, PR1625, PR1563,
PR1624, and PR2122 are C because M2 is below 5% and Matched below 2%, with no
valid root-preserving C amplification. PR1627 is D because M2 and Matched both
reach their thresholds; its aligned and restored controls preserve the root but
do not reduce M2 exposure. The other attempted alignments are root-changing or
type-invalid. NativePullTensor's earlier mixed result was a thread-local
root-ID collision; the atomic-root run above is the accepted partition.
PR1624 now reaches the expensive root; its prior E was caused by a stale or
unavailable instrumented-binary setup, and its broad C attempt changes the
root. Branch round5 base: `dataset/perf-issues`.
