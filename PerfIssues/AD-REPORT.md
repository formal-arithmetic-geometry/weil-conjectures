# PerfIssues Targeted Follow-up Experiments

Lean 4.35.0, snapshot `1ef1fddac73`, rerun with READY2-4.35.0 counters and
trace builds. Every row below is from the selected READY2 root for the same
root and variant used in the first pass. Trace path samples are inclusive
subtree samples; they are not additive with the root timer. Proposition timers
are nested and are not added to exclusive comparison/reduction totals.

| Case | READY2 root and path signal | Trace exclusive comparison / reduction | Dependent timer share | Expr proxy / RSS-commit proxy | A2/C conclusion |
|---|---|---:|---:|---:|---|
| NativePullTensor | `591`; `Functor.comp` paths 22,768.488 and 18,720.237 ms | 22,845.095 / 18,643.878 ms | 15,389.241 ms (67.4%) | 97,609,480 / 3.33 GB; 1.83 GB | `Functor.obj` premise A2 causal; B/C invalid |
| PR1556 | `826`; `CategoryStruct.comp`/`NatTrans.app` subtree 76,274.013 ms | 48,035.017 / 44,715.147 ms | 38,426.569 ms (80.0%) | 298,357,470 / 9.97 GB; 103 MB | `NatTrans.app` premise A2 causal; B/C invalid |
| PR1625 | `7086`; outer comp/app subtree 141,308.590 ms | 82,161.913 / 60,253.479 ms | 62,604.213 ms (76.2%) | 438,450,718 / 14.68 GB; 5.44 GB | outer `NatTrans.app` A2 causal; B/C invalid |
| PR1563 | `2754`; nested comp/coe subtree 25,812.968 ms | 15,785.269 / 12,913.573 ms | 12,565.977 ms (79.6%) | 112,996,826 / 3.78 GB; 0 B | distributed partial A2 only; B/C invalid |
| PR1627 | `1539`; generated algebra field chain 9,560.060 ms | 23,911.980 / 16,853.556 ms | 23,551.972 ms (98.5%) | 151,676,221 / 5.09 GB; 16.7 MB | no valid A2/B; C shared shape, unequal cost |
| PR1624 | `3034`; dependent Iso/comp endpoint 2,420.826 ms sample | 37,377.645 / 29,061.999 ms | 29,986.592 ms (80.2%) | 293,181,229 / 9.80 GB; 4.62 GB | A2/B invalid; C endpoint work confirmed |
| PR2122 | `32641`; branch endpoint path sample 192.071 ms | 12,314.071 / 11,839.551 ms | 8,546.240 ms (69.4%) | 84,397,734 / 2.81 GB; 1.53 GB | A/B invalid; C motive/witness valid |

The counters reruns were: NativePullTensor 22,407.489 ms;
PR1556 61,051.306 ms; PR1625 97,208.037 ms; PR1563 22,419.324 ms;
PR1627 29,196.986 ms; PR1624 52,710.009 ms; and PR2122 18,025.161 ms.
The corresponding comparison/reduction splits are recorded in each case
record and profile. The dependent share is the reported dependent-comparison
timer divided by trace comparison-exclusive time; it is a timer ratio, not a
claim that all dependent work is disjoint from proposition work.

READY2 also reports proposition comparison/reduction timers for every root;
the values are retained in each `EXPERIMENTS-AD.md` and `probes/ad/profile.txt`
because they are nested. C++ expression creation is the available allocation
proxy; RSS/commit deltas are process proxies and are not allocator totals.

The selected source variants remain the original in-situ or replay probes:
PR1627 uses `GeneratedProofPrefixes.lean`, while its original and replay
variants were retained as non-selected diagnostics. PR2122's standalone final
branch remains ill-typed outside its `Exists.casesOn` motive, so only the
motive and witness/predicate branch measurements are attributed.

All seven cases have updated per-case experiment records and compact READY2
profiles under `probes/ad/`. Raw rerun logs remain outside the committed
deliverables.
