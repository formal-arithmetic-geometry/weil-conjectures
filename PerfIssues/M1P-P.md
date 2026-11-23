# PerfIssues M1 propagation: part P (READY4.1)

All rows use fresh original-probe READY4.1 Lean 4.35.0 roots from this round,
not older MPRWE or kernel-validation measurements. Analyzer revision:
READY4.1 `mprwe_analyze.py`, kernel dataset commit `5ae674db0c7`.
Each run had a 3600 s limit. `O/analyzed` compares a separate counters run
with the trace aggregate for the same original probe and selected
process-wide root. Shares are comparison-exclusive time shares.

| Case | O/analyzed calls | M1 share | M1 calls | Max/median depth | 50% M1 time band | Mean fan-out | Dominant transition | Shape | C result |
|---|---:|---:|---:|---:|---:|---:|---|---|---|
| PR1556 | 6,670,198 / 6,670,198 | 99.671% | 5,006,059 | 213 / 122 | 87-126 | 1.330 | projection -> projection | mixed | no valid M0-preserving cut |
| PR1625 | 11,757,788 / 11,757,788 | 99.437% | 8,111,028 | 125 / 101 | 94-106 | 1.448 | projection -> projection | mixed | no valid M0-preserving cut |
| PR1624 | 6,598,545 / 6,598,545 | 99.782% | 5,215,138 | 88 / 60 | 52-64 | 1.265 | projection -> projection | mixed | not assigned |
| PR1563 | 2,563,145 / 2,563,145 | 99.617% | 1,924,504 | 93 / 57 | 49-62 | 1.331 | projection -> projection | mixed | not assigned |
| PR2122 | 2,257,184 / 2,257,184 | 97.330% | 1,797,805 | 87 / 50 | 46-58 | 1.219 | projection -> projection | mixed | not assigned |
| NativePullTensor | 2,685,580 / 2,685,580 | 98.299% | 1,120,689 | 81 / 44 | 34-46 | 2.375 | application -> function-head | mixed | no valid M0-preserving cut |
| PR1627 | 10,904,899 / 10,904,899 | 63.513% | 2,619,482 | 61 / 34 | 29-35 | 2.037 | failure outcome -> argument | wide | not assigned |

Aggregate and bounded raw-capture calls for each selected root:

| Case | Aggregate calls | Raw entered calls | Raw share |
|---|---:|---:|---:|
| PR1556 | 6,670,198 | 1,499 | 0.0225% |
| PR1625 | 11,757,788 | 1,703 | 0.0145% |
| PR1624 | 6,598,545 | 1,483 | 0.0225% |
| PR1563 | 2,563,145 | 1,748 | 0.0682% |
| PR2122 | 2,257,184 | 1,477 | 0.0654% |
| NativePullTensor | 2,685,580 | 1,723 | 0.0642% |
| PR1627 | 10,904,899 | 1,518 | 0.0139% |

The kernel accumulates complete per-label calls, exclusive times, depth
distributions, and all-label branch/child-kind transitions independently of
bounded raw enter/exit capture. The unchanged READY4.1 patch does not emit
complete M1-to-M1/Matched/M2 edge counts, provenance-split transition rows,
or mean fan-out by branch. Those missing fields are distinguished from raw
sample counts in the case reports. Path aggregation also groups deep calls
under `*` and sometimes `__other__`; PR1624's largest cost bucket is
`__other__`, so its true top individual path cannot be manually recovered.

The top all-label transition rows in the case reports exceed 90% of each
root's exclusive time. Subtracting all non-M1 time still leaves over 90%
of M1 exclusive time in those rows, including PR1627's control.
PR1627's label call counts are stable across READY3.2 and two fresh READY4.1
traces, but its exclusive-time shares move by more than 0.5 percentage
points between the fresh traces. The control report gives the measured
timing variance and the relation of its Matched work to M1 transitions.
