# PR1556: M1 propagation (READY4.1)

## Original root and validity

The original `OriginalNatTrans.lean` probe ran under the READY4.1 Lean 4.35.0
binary with a 3600 s limit. Process-wide root 6006 is the generated congruence
proposition domain, an `Eq`/`Eq` pair. The trace root completed with 6,670,198
calls and 47,950.904 ms comparison-exclusive time (80,124.863 ms root wall).
The original source's `NatTrans.app` major premise is represented within the
root's dependent argument path. The first structural divergence is recorded at
`root/fn/fn/arg/arg/fn/fn/fn/fn/fn/arg/fn/fn/fn/arg/fn/fn/fn/fn/arg/arg/fn`.

The separate fresh counters root also has 6,670,198 calls (63,379.010 ms root
wall and 31,280.366 ms comparison-exclusive). The trace count equals the
accepted READY3.2 count. Its M1 exclusive share, 99.671%, differs from that round's 99.622% by
0.049 percentage points. These older values are comparison controls only;
all READY4.1 measurements below are from this run.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.024 | <0.001% |
| M1 | 5,006,059 | 47,793.182 | 99.671% |
| M2 | 9,121 | 35.917 | 0.075% |
| Matched | 1,655,017 | 121.781 | 0.254% |
| Unclassified | 0 | 0 | 0% |

Analyzer revision: READY4.1 `mprwe_analyze.py` at kernel dataset commit
`5ae674db0c7`. Aggregate coverage is 6,670,198/6,670,198 calls. Raw capture
is 1,499 entered and 1,429 exited calls (1,499/6,670,198, 0.0225%). The
aggregate labels and times are computed in the kernel over every call, not
extrapolated from raw records. Depth calls and exclusive/reduction times sum
exactly to label totals; 6,670,197 transition edges plus the 0.024 ms root
direct time sum to the root. No depth was clamped.

## A2: topology

M1 depth: mean 133.587, median 122, p90 181, p99 193, max 213. The narrowest
contiguous bands holding 50% and 90% of M1 exclusive time are depths 87-126
and 88-186. The depth histogram is binned by tens below (calls; exclusive ms).

| Depth | 0-49 | 50-79 | 80-109 | 110-139 | 140-169 | 170-199 | 200-213 |
|---|---:|---:|---:|---:|---:|---:|---:|
| M1 calls | 1,601 | 138,728 | 1,521,972 | 1,264,569 | 808,865 | 1,263,909 | 6,415 |
| M1 ms | 17.8 | 1,177.9 | 14,287.6 | 13,349.6 | 7,306.8 | 11,588.1 | 65.3 |

M1-parent fan-out (all child labels): mean 1.330, median 1, p90 3, max 21.
Exact histogram: 0:1,613,021; 1:1,982,500; 2:532,540; 3:510,719;
4:260,022; 5:7,545; 6:33,312; 7:24,911; 8:823; 9:6,915;
10:981; 11:372; 12:5; 13:7; 14:19,278; 21:13,108.
In bounded raw capture, 1,006 M1-parent children are M1, 484 are Matched,
and 2 are M2. The patch does not aggregate parent-label by child-label,
so complete M1-to-M1/Matched/M2 edge counts are unavailable. These raw counts
are observed sample counts, not root totals.

This is **mixed** propagation: the M1 chain reaches depth 213, while
applications and projections repeatedly spawn multiple children across
the expensive depths. The two named M1 path buckets below account for
47,792.288 ms of M1 exclusive time.

## A3: branch transition matrix

Rows are complete over all child labels. The first five account for
45,387.889 ms, 94.65% of root exclusive time, so they also bound the
dominant M1 work within the 0.329% non-M1 contribution. Mean fan-out by
branch is not emitted by READY4.1; the M1-parent aggregate mean above is
available. `failure_followup` is 0 in the top two rows.

| Parent branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| projection | projection | 1,289,241 | 18,938.087 |
| application | argument | 2,647,095 | 13,493.380 |
| second_whnf | fallback | 542,686 | 6,737.477 |
| application | function-head | 1,226,204 | 3,450.295 |
| quick | dependent-body | 155,587 | 2,768.650 |
| proof_irrelevance | proposition-type | 126,864 | 1,330.286 |
| lazy_delta | argument | 328,642 | 752.938 |
| remaining rows | mixed | 353,878 | 479.767 |

The two highest named M1 aggregate buckets are
`root/argument[1]/argument[0]/argument[7]/argument[0]/argument[0]/*`
(4,012,007 calls; 39,491.626 ms) and the corresponding `argument[6]` path
(993,999 calls; 8,300.662 ms). The `*` suffix is the analyzer's bounded
path grouping, not a single reconstructed subtree.

## A4: first transitions of the costly paths

The raw root pair is `Eq`/`Eq`; its function-head child is Matched, while
call 3 compares `Quiver.Hom`/`Quiver.Hom` as application argument 0 and
retains the root divergence hashes (M1). Call 4 compares
`CategoryStruct.comp`/`CategoryStruct.comp` as argument 1 (M2 after
reduction). In that argument, calls 12-15 move through
`CategoryStruct.comp` -> `DFunLike.coe` (argument 7, M1) ->
`Equiv.proj` (function head, M1) -> `equivShrink` (projection, M1).
The child's divergence hashes match its parent's in each M1 step; reduction
changes the exposed head without erasing the inherited mismatch.

The dominant `argument[7]` aggregate path follows the application argument
comparison at the `DFunLike.coe`/`DFunLike.coe` pair, then descends through
projection and another argument comparison. Its sibling `argument[6]` bucket
is generated by the same application loop on the preceding argument; both
remain below the M0 major-premise comparison. `is_def_eq_app` compares the
function and then each argument at `type_checker.cpp:1628-1645`, and
`lazy_delta_proj_reduction` re-enters comparison on projected components at
`:1857-1880` (source audit `M1P-KERNEL.md`). The bounded raw window does not
retain a complete call tree for either multi-million-call bucket, so deeper
exact pairs and per-subtree maximum fan-out cannot be recovered from it.

## C: M0-preserving cut point

The candidate is the argument-6/7 major-premise continuation above. The
existing source-level alignment replaces the major premise required by the
dependent `NatTrans.app` argument and thereby changes the inferred domain of
the generated congruence proof. That removes the original M0 pair. Keeping
that same domain while replacing only the descendant would require a term
at the original dependent type; the available aligned proof inhabits the
changed domain. No type-correct M0-preserving cut was constructed, so no
O-cut/O-restore workload comparison is claimed. O is the measured original
above; the byte-identical restored snapshot is a source identity check,
not a selective intervention.
