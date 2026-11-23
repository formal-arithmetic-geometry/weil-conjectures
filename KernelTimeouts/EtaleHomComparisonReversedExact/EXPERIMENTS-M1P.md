# EtaleHom M1 propagation (READY4.2)

Fresh O uses `EtaleHomComparisonReversedExact/probes/mprwe/Original.lean`
from the reserved `m1p` import tree (revision `105ac3f5b23`), Lean 4.35.0,
and the READY4.2 kernel/analyzer (`0311a15b5f4`). The selected root is
2632, the instantiated `hv` argument of
`derivedTensorHomShiftComparison_component`.

| Check | Result |
|---|---:|
| O counters / analyzed calls | 3,180,470 / 3,180,470 |
| Raw entered calls | 4,124 (0.130%) |
| M1 calls / call share | 2,390,795 / 75.171% |
| M1 exclusive-time share | 99.735% |
| M1 / M2 / Matched time shares | 99.735% / 0.002% / 0.263% |

Aggregate labels, transitions, depth, and fan-out cover all 3,180,470
calls; the raw stream is only the bounded manual-review sample. The root
call count is unchanged from READY4.1. The M1 share is within 0.5 pp of the
READY4.1 result.

## A2: depth and shape

M1 depth mean/median/p90/p99/max is 78.707/79/90/97/111. The 50% and 90%
exclusive-time bands are 71--83 and 63--92. Fan-out mean/median/p90/max is
1.330/1/3/28. The analyzer rule classifies this as **deep** (median >= 75,
mean fan-out <= 1.5, 90%-time width <= 32).

M1-parent edge counts are M1->M1 2,390,783, M1->Matched 789,627, and
M1->M2 15. The dominant M1 propagation is a long projection/application
chain with small repeated branching.

## A3: M1-parent matrix

Rows are keyed by parent label, child label, initiating branch, and child
kind. They cover 94.9% of M1 exclusive time; no outcome is used as a branch.

| Parent | Child | Branch / kind | Calls | Exclusive ms | Mean fan-out |
|---|---|---|---:|---:|---:|
| M1 | M1 | projection / projection | 626,927 | 9,131.177 | 1.000 |
| M1 | M1 | application / argument | 699,876 | 6,421.225 | 3.924 |
| M1 | M1 | second_whnf / whnf-iota-exposure | 255,580 | 3,478.309 | 1.000 |
| M1 | M1 | application / function-head | 449,472 | 1,732.476 | 2.506 |
| M1 | M1 | quick / dependent-body | 73,549 | 1,277.882 | 2.806 |

## A4: path reconstruction

The new matrix leaves the READY4.1 dominant transition unchanged, so the
manual reconstruction is retained. The root M0 pair is
`IsEtaleHomTranspose <> 7`, with the first divergence at the stored `hv`
argument.

1. Binder instantiation compares `Eq <> Eq` through the dependent-body path
   in `is_def_eq_binding` (`M1P-KERNEL.md`, 4.35.0 line 1479). The
   instantiated body keeps the `hv` mismatch hashes, so the child is M1.
2. Application congruence compares `DFunLike.coe <> DFunLike.coe` through
   `is_def_eq_app` (line 1628). Matching heads do not remove the divergent
   argument lineage.
3. WHNF and projection exposure continue through `EquivLike.coe`,
   `Equiv.toFun`, `Equiv.invFun`, and projection children in
   `is_def_eq_core`/`lazy_delta_proj_reduction` (lines 1909 and 1857).

The bounded raw sample is not used to rank complete-root costs.

## C

The dependent `hv` endpoint remains the only candidate. Replacing its child
while retaining the original dependent type is not type-correct; transporting
the whole proposition changes M0. The step-2 result therefore stands: no
M0-preserving cut and no causal speedup.
