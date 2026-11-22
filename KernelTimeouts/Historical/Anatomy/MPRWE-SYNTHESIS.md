# MPRWE Cross-case Synthesis

The historical Cone row below uses a fresh READY3 4.33.1 counter run and a
bounded READY3 trace. The current KernelTimeouts and PerfIssues rows use the
READY2 fallback reports produced before READY3 was available; their recursive
provenance is intentionally Unclassified. Shares are reported for the
selected root only, and inclusive path samples are not added to exclusive
root time.

| Case | Strict matched baseline | Root calls / exclusive comparison | M1 share | M2 share | Matched share | Unclassified | Selective M2 alignment | Outcome |
|---|---|---:|---:|---:|---:|---:|---|---|
| Derived-Completion Cone | No, A3 | 12.221M / 51.518 s | unavailable | unavailable | unavailable | 100% | unavailable; all controls change root | E |
| FiniteBaseChange | No, A3 | 239.341M / 611.980 s | unavailable | unavailable | unavailable | 100% | invalid whole-root transport | E |
| IntegralComparison | No, A3 | 9.426M / 44.816 s | unavailable | unavailable | unavailable | 100% | invalid first-leaf control | E |
| RealPurity | No, A3 | 17.310M / 53.949 s | unavailable | unavailable | unavailable | 100% | invalid ring alignment | E |
| OrderedSpectralRawLattices | No, A3 | 18.945M / 51.938 s | unavailable | unavailable | unavailable | 100% | invalid route alignment | E |
| EtaleHom | No, A3 | 3.180M / 12.301 s | unavailable | unavailable | unavailable | 100% | invalid whole-domain transport | E |
| F66Adj | No, A3 | 3.898M / 15.058 s | unavailable | unavailable | unavailable | 100% | invalid whole-counit transport | E |
| ImageHomCounit | No, A3 | 6.360M / 25.076 s | unavailable | unavailable | unavailable | 100% | invalid endpoint alignment | E |
| RealPushforward | No, A3 | 17.340M / 52.018 s | unavailable | unavailable | unavailable | 100% | invalid polynomial alignment | E |
| NativePullTensor | No, A3 | 2.686M / 15.349 s | unavailable | unavailable | unavailable | 100% | unavailable; provider alignment removes M0 | E |
| PR1556 | A1 diagnostic | 6.670M / 34.922 s | unavailable | unavailable | unavailable | 100% | unavailable; major-premise alignment removes M0 | E |
| PR1625 | A1 diagnostic | 11.758M / 59.141 s | unavailable | unavailable | unavailable | 100% | unavailable; outer alignment removes M0 | E |
| PR1563 | No, A3 | 2.574M / 15.785 s | unavailable | unavailable | unavailable | 100% | invalid provider change | E |
| PR1624 | No, A3 | 6.599M / 37.378 s | unavailable | unavailable | unavailable | 100% | invalid endpoint alignment | E |
| PR1627 | No, A3 | 10.905M / 23.912 s | unavailable | unavailable | unavailable | 100% | invalid generated-field alignment | E |
| PR2122 | No, A3 | 2.227M / 11.486 s (historical) | unavailable | unavailable | unavailable | 100% | unavailable; imported olean missing | E |

## Answers to the research questions

1. No case is defensibly classified as dominated by expensive matched descendants, newly exposed mismatches, or inherited propagation. The available measurements cannot separate those categories.
2. Selective M2 alignment has not been demonstrated. Every attempted control either changes the root obligation or removes M0; those controls are invalid for C.
3. The robust result is diagnostic: smaller matched comparisons can be cheap while the full dependent root remains expensive. This does not identify the mechanism inside the full root.
4. The measured workload spans both mixed comparison/reduction roots and comparison-heavy roots, but the mechanism split remains unresolved in every row.
5. The measured unclassified share is 100% for provenance attribution in all selected roots. The READY3 Cone trace now contains the required raw fields and reduction predecessors; its bounded capture is not a complete cost attribution.

The next valid step is a selected-root READY3 trace with a sufficiently large
but bounded event sample, manual expression-boundary review, and a type-correct
descendant alignment that preserves the original root telescope and M0.
