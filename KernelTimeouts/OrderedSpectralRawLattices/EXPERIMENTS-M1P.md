# OrderedSpectralRawLattices M1 propagation (READY4.1)

Fresh O is `probes/mprwe/Original.lean` on Lean 4.35.0, current import
revision `15b8acba63e`, READY4.1 kernel/analyzer revision `5ae674db0c7`.
The expensive original root is 62844. O counters and analyzed root both
record 18,944,709 calls, exactly the accepted READY3.2 count. Counter
root wall/comparison/reduction are 41,558.650/41,538.598/20.052 ms;
trace comparison exclusive is 65,972.799 ms. Aggregate coverage is
18,944,709/18,944,709; raw entered coverage is 4,333/18,944,709
(0.023%). The deterministic kernel timeout is the expected O outcome.

| Label | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.186 | 0.000% |
| M1 | 8,320,909 | 42,435.667 | 64.323% |
| M2 | 3,499,646 | 23,019.941 | 34.893% |
| Matched | 7,124,151 | 516.939 | 0.784% |
| Unclassified | 2 | 0.066 | 0.000% |

M1's time share differs from the accepted READY3.2 share by more than
0.5 percentage points, although the M1, M2, and Matched call counts and the root call
count are identical. The difference is exclusively measured time
weighting, consistent with READY4.1's extra branch/depth bookkeeping
and run-to-run timing variation in the mixed failure path. It is not
a change in selected root or provenance calls.
Counter and trace times are separate runs.

## A2: depth and fan-out

M1 depth mean/median/p90/p99/max is 63.572/64/68/70/71.
The narrowest 50% and 90% M1 exclusive-time bands are 60--65 and
59--69. M1 fan-out mean/median/p90/max is 1.754/1/8/18.
Its count histogram is 0: 3,091,705; 1: 3,397,060; 2: 966,618;
3: 121; 4--9: 49,692; 10+: 815,713. No depth was clamped.
This is mixed deep/wide propagation: work stays near depth 64 and many
M1 nodes open at least ten children. In the bounded raw sample, M1
parents have 1,596 M1, 2,596 Matched, and 32 M2 child edges; these
are not whole-root label-edge totals.

## A3: transition matrix

The four largest complete-root rows total 62,902.431 ms. Even if all
23,537.132 ms of non-M1 time fell in those rows, they still contain at
least 92.7% of M1 time. READY4.1 does not emit label-specific row counts
or row mean fan-out.

| Parent outcome/branch | Child kind | Calls | Exclusive ms |
|---|---|---:|---:|
| lazy_delta | dependent-body | 724,758 | 16,339.487 |
| failure | argument | 6,867,814 | 16,285.415 |
| failure | field | 4,350,210 | 15,502.184 |
| failure | projection | 3,625,599 | 14,775.345 |

The transition matrix has 18,944,708 child calls, equal to root calls
minus one. Here `failure` is the final outcome recorded for a parent,
not the initiating kernel comparison branch of each child. It cannot
establish a single M1-generating strategy. In the raw M1-to-M1 sample,
argument children lead (1,255), then fallback (230), projection (57),
and proposition-type (50). The raw argument descent resembles the
NativePullTensor primary strategy in `M1P-KERNEL.md`; the Cone and
EtaleHom primary roots instead have projection descent as their largest
complete-root row. With 34.893% M2 time and no label-specific
transition rows, whether either primary strategy remains M1-dominant
here is unresolved.
