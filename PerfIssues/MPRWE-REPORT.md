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
