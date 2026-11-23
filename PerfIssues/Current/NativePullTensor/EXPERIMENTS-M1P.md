# NativePullTensor: M1 propagation (READY4.2)

## Validation

This case uses K's fresh READY4.2 aggregate trace for the original
`OriginalRoot.lean` probe, root 18506, plus my separate READY4.2 counters
run of the same probe and root selection. Both have 2,685,580 calls. The
READY4.2 trace has M1 98.164%, M2 0.318%, and Matched 1.517%, within 0.5
percentage points of READY4.1 (98.299%).

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.012 | 0.000% |
| M1 | 1,120,689 | 22,282.538 | 98.164% |
| M2 | 12,041 | 72.264 | 0.318% |
| Matched | 1,552,849 | 344.437 | 1.517% |
| Unclassified | 0 | 0 | 0.000% |

Analyzer: READY4.2 `mprwe_analyze.py`, kernel dataset commit
`0311a15b5f4`. Aggregate coverage is 2,685,580/2,685,580 calls; K's run
has 0 raw enter/exit records. The complete matrix reconciles to 2,685,579
child edges plus 0.012 ms root-direct time. No depth was clamped.

## A2: topology

M1 depth mean/median/p90/p99/max is 43.511/44/55/65/81. The narrowest
bands containing 50% and 90% of M1 exclusive time are 36-47 and 26-56.
M1-parent fan-out mean/median/p90/max is 2.375/0/9/28. M1 -> M1,
M1 -> Matched, and M1 -> M2 edges are 1,114,699, 1,534,880, and 12,037.
The analyzer verdict is **wide**.

## A3: M1-parent transition matrix

The first seven rows cover 99.0% of M1 exclusive time.

| Initiating branch | Child kind | Child label | Calls | Child exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| application | function-head | M1 | 104,412 | 6,773.125 | 2.232 |
| application | argument | M1 | 328,226 | 6,455.985 | 4.775 |
| lazy_delta | argument | M1 | 531,078 | 4,672.640 | 7.766 |
| projection | projection | M1 | 59,456 | 1,992.740 | 1.000 |
| second_whnf | whnf-iota-exposure | M1 | 27,189 | 1,024.181 | 2.321 |
| quick | dependent-body | M1 | 32,260 | 674.072 | 1.001 |
| proof_irrelevance | proposition-type | M1 | 32,058 | 665.071 | 1.000 |

The dominant M1 transition is application function-head congruence. Lazy
delta argument descent is the next major branch. The principal non-M1 row
is lazy-delta argument M1 -> Matched (1,084,558 calls, 273.742 ms).

## C: M0-preserving cut point

The selected expensive paths are the two `Exists.choose` domains. Replacing
either provider changes the dependent argument's required type and removes
the original M0. No type-correct local replacement preserving the same
telescope was constructed, so C remains blocked by the provider-dependent
type. No O-cut/O-restore cost claim is made.
