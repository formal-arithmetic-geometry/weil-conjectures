# READY4.1 M1 propagation: Derived-Completion Cone

## Setup and root identity

This run uses the historical 4.33.1 project revision that contains the full
Derived-Completion Cone root, with the READY4.1 4.33.1 kernel. The selected
process-wide root is 1849, run with one Lean worker and the existing Cone
probe in the historical import closure. The root completed with 12,220,746
successes and 76 timeout/failure exits. It measured 12,220,822 recursive
calls. READY4 measured 12,220,818 and the accepted READY3.2 control measured
12,220,823. The four-call change from READY4 occurs at the deterministic
timeout boundary under added observational bookkeeping; the root operation
and conversion rules are unchanged.

The READY4.1 root totals are complete kernel aggregates:

| label | calls | exclusive ms | time share |
|---|---:|---:|---:|
| M0 | 1 | 0.067 | 0.000% |
| M1 | 9,356,262 | 86,644.293 | 99.694% |
| M2 | 9,087 | 55.712 | 0.064% |
| Matched | 2,855,469 | 210.463 | 0.242% |
| Unclassified | 3 | 0.121 | 0.000% |
| **root** | **12,220,822** | **86,910.655** | **100%** |

The transition rows contain 12,220,821 child edges and 86,910.589 ms of
exclusive time; adding the 0.067 ms root direct time gives the root total.
The largest unknown/unclassified time is 0.121 ms, far below 5%.

## A1/A3: complete transition matrix

The matrix is complete over all calls, not limited to the bounded raw trace.
Rows are parent branch, child kind, calls, exclusive time, and reduction time.

| parent | child kind | calls | exclusive ms | reduction ms |
|---|---|---:|---:|---:|
| projection | projection | 2,951,994 | 38,999.493 | 4,880.914 |
| application | argument | 4,542,956 | 21,805.155 | 20,794.428 |
| second_whnf | fallback | 1,053,662 | 11,870.094 | 30,156.686 |
| application | function-head | 2,133,228 | 6,589.977 | 454.517 |
| quick | dependent-body | 240,541 | 3,655.561 | 1,184.778 |
| proof_irrelevance | proposition-type | 187,630 | 2,201.870 | 57.967 |
| lazy_delta | argument | 684,531 | 1,401.078 | 887.775 |
| projection | argument | 77,846 | 278.985 | 193.032 |
| quick | binder-domain | 343,910 | 74.852 | 0.156 |
| lazy_delta | dependent-body | 4,313 | 30.491 | 53.392 |
| all exception/fallback rows | other kinds | 210 | 3.032 | 5.078 |

`failure_followup` was zero in every selected row. This means the observed
root's propagation is ordinary recursive descent and reduction continuation,
not repeated immediate retry after a failed child.

## A2: depth and fan-out

M1 exact depth has mean 81.742, median 82, p90 93, p99 100, and maximum
111. The narrowest contiguous depth bands containing 50% and 90% of M1
exclusive time are 76--88 and 66--96. M1 fan-out has mean 1.305, median 1,
p90 3, and maximum 28. M2 depth has mean 56.520, median 51, p90 78,
p99 83, and maximum 84; Matched depth has mean 79.522, median 80, p90
93, p99 100, and maximum 111. No calls were clamped above depth 4096.
Every label's depth calls and exclusive/reduction time sum to its label
totals. The high depth and nontrivial fan-out show a deep and wide tree:
long projection/application chains repeatedly branch into arguments and
dependent checks.

## A4: manual first-transition reconstruction

At the root, the original pair is the `inlineCone` conversion against its
declared `Cone (quotPowFunctor J I ⋙ tensorLeft K)` type. The first useful
descent is application congruence: `is_def_eq_app` compares function heads,
then corresponding arguments. The argument child inherits M1 because it is
the same parent pair's corresponding argument after the function-head
obligation has been established; it is not a new mismatch.

The dominant path then repeatedly compares projection applications. In
`lazy_delta_proj_reduction`, the projection components are exposed and
re-enter `is_def_eq_core`; each component comparison retains the parent
divergent hashes and is therefore M1. When WHNF exposes an application,
`is_def_eq_app` creates a function-head child followed by argument children.
For dependent fields, `is_def_eq_binding` instantiates the binder and creates
the dependent-body child. Proof-valued fields use
`is_def_eq_proof_irrel`, which creates a proposition-type child after both
proof terms infer `Prop` types.

The dominant projection-to-projection transition has 2,951,994 child calls and
38,999.493 ms exclusive time. The largest application-argument transition has
4,542,956 calls and 21,805.155 ms. These are direct branch transitions, not
labels inferred from a bounded event sample.

## Instrumentation validity and overhead

M1/M2/Matched shares are accumulated by the kernel for every comparison in
the selected root. Calls absent from raw enter/exit records are classified by
the same complete comparison object and its parent divergence metadata. The
Cone trace retained 211 entered and 195 exited raw records, while aggregate
coverage was 12,220,822/12,220,822 calls. The transition and per-label
exclusive aggregates are therefore complete; raw records are only for manual
path review. READY4 root wall time was 121.553 s in counters mode and
the fresh READY4.1 trace root wall time was 145.579 s. Existing READY3.2 paired controls reported a
163.549 s counter root span and 147.133 s trace root span for the accepted
12,220,823-call control; these timings are reported as paired measurements,
not normalized overhead claims, because the historical project/build and
timeout boundary differ.

## C: cut-point intervention

The original Cone alignment target is a dependent provider/field comparison.
Replacing that descendant with an aligned provider changes the dependent
telescope and consequently changes the root conversion obligation; it does
not preserve M0. The attempted O-cut was therefore rejected as invalid.
The required control is:

| variant | root M0 | root calls | status |
|---|---|---:|---|
| O | preserved | 12,220,822 (READY4.1; 12,220,823 accepted control) | valid baseline |
| O-cut | not demonstrably preserved | not used | rejected: telescope/root changed |
| O-restore | preserved | 12,220,818 (READY4) | restored baseline |

O and O-restore are the same original source and root operation. No causal
speedup is claimed because no type-correct M0-preserving descendant
replacement was available. This is a limitation of the intervention, not a
substitution of a smaller consumer or a different theorem.
