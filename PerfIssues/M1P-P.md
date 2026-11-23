# PerfIssues M1 propagation: part P (READY4.2)

All rows below use fresh READY4.2 original-probe runs. The 4.35.0 probes
import from the reserved `m1p` tree. Analyzer: READY4.2
`mprwe_analyze.py`, kernel dataset commit `0311a15b5f4`. Aggregate labels,
exclusive times, depth distributions, and the provenance-keyed transition
matrix cover every call; bounded enter/exit capture is reported separately.
The counters run is a separate fresh run of the same probe and selected root.

| Case | Calls (counter / analyzed) | M1 call share | M1 time share | M1 calls | Depth median / p90 / max | 50% band | Mean fan-out / p90 | M1 -> M1 / Matched / M2 | Dominant M1 transition | Shape | C |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---|---|
| PR1556 | 6,670,198 / 6,670,198 | 75.051% | 99.707% | 5,006,059 | 122 / 181 / 213 | 87-125 | 1.330 / 3 | 5,003,086 / 1,649,139 / 7,606 | projection -> projection | mixed | blocked: dependent domain |
| PR1625 | 11,757,788 / 11,757,788 | 68.984% | 99.546% | 8,111,028 | 101 / 112 / 125 | 95-107 | 1.448 / 3 | 8,104,569 / 3,638,816 / 3,907 | projection -> projection | deep | blocked: dependent domain |
| PR1624 | 6,598,545 / 6,598,545 | 79.035% | 99.848% | 5,215,138 | 60 / 70 / 88 | 57-68 | 1.265 / 3 | 5,214,946 / 1,382,892 / 193 | projection -> projection | mixed | not assigned in step 2 |
| PR1563 | 2,563,145 / 2,563,145 | 75.084% | 99.731% | 1,924,504 | 57 / 70 / 93 | 51-63 | 1.331 / 3 | 1,924,060 / 637,204 / 773 | projection -> projection | mixed | not assigned |
| PR2122 | 2,257,184 / 2,257,184 | 79.648% | 98.113% | 1,797,805 | 50 / 60 / 87 | 42-54 | 1.219 / 3 | 1,753,186 / 384,748 / 51,716 | projection -> projection | mixed | not assigned |
| PR1627 (3 repeats) | 10,904,899 / 10,904,899 | 24.021% | 64.767% [64.1-65.2] | 2,619,482 | 34 / 37 / 61 | 29-35 | 2.037 / 9 | 1,180,833 / 2,662,551 / 1,492,777 | quick -> dependent-body (M1 -> M1) | wide | control; no cut |
| NativePullTensor (K trace) | 2,685,580 / 2,685,580 | 41.730% | 98.164% | 1,120,689 | 44 / 55 / 81 | 36-47 | 2.375 / 9 | 1,114,699 / 1,534,880 / 12,037 | application -> function-head | wide | blocked: provider-dependent type |

PR1627's three READY4.2 traces have identical calls and edge counts. Their
M1 exclusive-time shares are 64.767%, 64.064%, and 65.196%; the table gives
the median and minimum--maximum spread. Its M1 -> Matched work is mostly
application-argument children (1,935,770 calls, 3,163 ms in the first
repeat), sharing the generated-field application path that carries the M1
lineage.

Raw capture entered 1,499/6,670,198 calls (PR1556), 1,703/11,757,788
(PR1625), 1,483/6,598,545 (PR1624), 1,748/2,563,145 (PR1563),
1,477/2,257,184 (PR2122), and 1,518/10,904,899 (each PR1627 repeat).
NativePullTensor uses K's READY4.2 aggregate run, with a fresh counters
run confirming its 2,685,580-call root; K's run has no raw enter/exit
records. The aggregate coverage is complete in every case, so these small
raw windows are used only for manual path checks.
