# PerfIssues MPRWE Cross-case Synthesis

Kernel: READY2-4.35.0. READY3 was absent; all descendant labels below are
limited by missing parent IDs, paths, and reduction before/after events.
Strict A0 matched roots: none. The diagnostic baselines are A1/A3 as recorded
per case. Shares are measured only for the attributable trace total; the
recursive portion is explicitly Unclassified rather than guessed.

| Case | Baseline | M1 calls/time | M2 calls/time | Matched calls/time | Unclassified | Selective M2 alignment | Outcome |
|---|---|---|---|---|---|---|---|
| NativePullTensor | A3, regular provider 1 ms | unknown | unknown | unknown | 2,685,579 / 15,349.294 ms | unavailable; root provider alignment invalid | E |
| PR1556 | A1, 284,842 / 1,055.447 ms | unknown | unknown | unknown | 6,670,197 / 34,922.251 ms | unavailable; major premise alignment removes M0 | E |
| PR1625 | A1, below threshold | unknown | unknown | unknown | 11,757,787 / 59,140.866 ms | unavailable; outer major alignment removes M0 | D/E |
| PR1563 | A3, 1 ms | unknown | unknown | unknown | 2,573,988 / 15,785.269 ms | unavailable; provider change alters dependent root | D/E |
| PR1624 | A3, 0.050 ms | unknown | unknown | unknown | 6,598,544 / 37,377.645 ms | unavailable; endpoint alignment changes telescope | D/E |
| PR1627 | A3, 0.009 ms | unknown | unknown | unknown | 10,904,898 / 23,911.980 ms | unavailable; generated-field alignment removes M0 | D/E |
| PR2122 | A3, 0.038 ms historical | unknown | unknown | unknown | historical root only / 11,486 ms | unavailable; missing GmRelativeKummer.olean | E |

The existing O/A/R measurements establish that major premise/provider
alignment is reversible in PR1556, PR1625, NativePullTensor, and PR1624, but
they are not selective C controls. No case can be classified as M2-dominated
from READY2. The only robust cross-case statement is that diagnostic matched
children can be cheap while the full dependent root remains expensive; the
remaining mechanism is unresolved between M1, M2, and expensive matched
descendants.

## MPRWE round 2

Round 2 uses READY3.1-4.35.0 counters and traces on fresh probes. Aggregate
provenance records partition each selected root's complete exclusive time;
raw enter/exit records were capped at 4,000 events and often covered earlier
roots. Strict A0 matched roots remain unavailable; baselines are the recorded
A1/A3 diagnostics.

| Case | Selected root calls / exclusive ms | M0 | M1 | M2 | Matched | Unclassified | C and outcome |
|---|---:|---:|---:|---:|---:|---:|---|
| NativePullTensor | 2,685,580 / 20,675.658 | 0.000% | 98.124% | 0.299% | 1.581% | 0.000% | Root provider alignment invalid; no child-only M2 control. **C** |
| PR1556 | 6,670,198 / 45,113.186 | 0.000% | 99.700% | 0.072% | 0.228% | 0.000% | Major-premise alignment invalid; no child-only M2 control. **C** |
| PR1625 | 11,757,788 / 68,508.492 | 0.001% | 99.471% | 0.071% | 0.456% | 0.001% | Outer-major alignment invalid; no child-only M2 control. **C** |
| PR1563 | 2,573,989 / 17,289.421 | 0.000% | 99.733% | 0.025% | 0.241% | 0.001% | Provider alignment invalid; no child-only M2 control. **C** |
| PR1624 | 6,598,545 / 40,848.850 | 0.000% | 99.809% | 0.006% | 0.185% | 0.001% | Endpoint alignment invalid; no child-only M2 control. **C** |
| PR1627 | 10,904,899 / 28,458.907 | 0.000% | 66.352% | 24.928% | 8.727% | 0.000% | Generated-field alignment invalid; no child-only M2 control. **D** |
| PR2122 | 2,227,198 / 13,821.715 | 0.000% | 98.901% | 0.876% | 0.201% | 0.021% | Recursor branch extraction invalid; no child-only M2 control. **C** |

Shares are rounded from aggregate exclusive nanoseconds; M0 rounds to zero in
every case. PR1627 is the only case with a substantial M2 share. In all other
cases the workload is inherited M1 work, with matched descendants below 2%.

The O and R source snapshots are byte-identical for the retained probes, so R
restores the original root mismatch but is not a selective C intervention.
The attempted C replacements change the root provider, motive, telescope, or
generated domain and are recorded as invalid rather than treated as causal
alignments. Earlier R timings are labeled in the per-case reports.

PR2122's `GmRelativeKummer.olean` is present. Its fresh counter and trace runs
reproduced the historical 2,227,198-call root, resolving the round-1 dependency
claim; the fresh root is classified above.
