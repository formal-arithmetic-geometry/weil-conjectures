# KernelTimeouts M1 propagation: part T

All measured rows are fresh READY4.1 Lean 4.35.0 runs on the expensive
original root with the case's O probe, at current import revision
`15b8acba63e`. Kernel/analyzer revision is dataset commit
`5ae674db0c7` (analyzer SHA-256 prefix `7e2ee5f4e23895e3`). The
comparison shares use complete-root exclusive time; the raw trace is
bounded. Counter and trace call counts agree in every measured row.

| Case | M1 share | M1 calls | M1 max / median depth | 50% time band | Mean fan-out | Largest complete-root transition | Shape | C result |
|---|---:|---:|---:|---|---:|---|---|---|
| EtaleHom | 99.724% | 2,390,795 | 111 / 79 | 71--83 | 1.330 | projection to projection | mixed | no M0-preserving cut at dependent `hv` endpoint |
| FiniteBaseChange | 72.981% | 130,197,227 | 87 / 75 | 71--74 | 1.081 | failure to projection (all labels) | mixed | local candidate leaves O workload; no valid cut |
| RealPurity | unavailable | unavailable | unavailable | unavailable | unavailable | unavailable | unavailable | O blocked by missing imported `.olean` |
| OrderedSpectralRawLattices | 64.323% | 8,320,909 | 71 / 64 | 60--65 | 1.754 | lazy-delta to dependent body (near tie with failure to argument) | mixed | not requested |
| RealPushforward | 62.315% | 8,002,209 | 89 / 84 | 82--84 | 1.274 | failure to projection | mixed | not requested |
| IntegralComparison | 99.568% | 6,680,842 | 181 / 109 | 93--113 | 1.406 | projection to projection | mixed | not requested |
| F66Adj | 99.722% | 2,961,163 | 121 / 90 | 82--96 | 1.316 | projection to projection | mixed | not requested |
| ImageHomCounit | 99.774% | 4,781,271 | 204 / 162 | 154--166 | 1.330 | projection to projection | mixed | not requested |

`READY4.1` emits complete branch/kind rows but does not key them by child
provenance or report row mean fan-out. In mixed roots, the listed largest
row cannot be treated as the dominant M1-only transition. A `failure`
parent label records the parent's final outcome rather than the precise
branch initiating each child. The case reports give conservative M1 time
coverage bounds and sampled label-to-label edges. The kernel patch was
not changed.
