# READY4 M1 propagation: Derived-Completion Cone

## Setup and root identity

This run uses the historical 4.33.1 project revision that contains the full
Derived-Completion Cone root, with the READY4 4.33.1 kernel. The selected
process-wide root is `1869`, run with one Lean worker and the existing Cone
probe. The root completed with 12,220,742 successes and 76 timeout/failure
exits. Counters and trace runs selected the same root and both measured
12,220,818 recursive calls. The accepted READY3.2 control was 12,220,823
calls; the five-call difference is a deterministic timeout-boundary shift
under the extra branch metadata and locking bookkeeping, not a change to the
root operation or conversion rules.

The READY4 root totals are complete kernel aggregates:

| label | calls | exclusive ms | time share |
|---|---:|---:|---:|
| M0 | 1 | 0.063 | 0.000% |
| M1 | 9,356,259 | 86,179.330 | 99.685% |
| M2 | 9,087 | 55.316 | 0.064% |
| Matched | 2,855,468 | 217.044 | 0.251% |
| Unclassified | 3 | 0.124 | 0.000% |
| **root** | **12,220,818** | **86,451.877** | **100%** |

The transition rows contain 12,220,817 child edges and 86,451.813 ms of
exclusive time; adding the 0.063 ms root direct time gives the root total.
The largest unknown/unclassified time is 0.124 ms, far below 5%.

## A1/A3: complete transition matrix

The matrix is complete over all calls, not limited to the bounded raw trace.
Rows are parent branch, child kind, calls, exclusive time, and reduction time.

| parent | child kind | calls | exclusive ms | reduction ms |
|---|---|---:|---:|---:|
| projection | projection | 2,951,993 | 38,983.983 | 4,811.374 |
| application | argument | 4,542,955 | 21,618.337 | 20,542.336 |
| second_whnf | fallback | 1,053,662 | 11,712.799 | 29,870.911 |
| application | function-head | 2,133,227 | 6,580.179 | 452.629 |
| quick | dependent-body | 240,541 | 3,619.643 | 1,170.122 |
| proof_irrelevance | proposition-type | 187,630 | 2,159.578 | 57.217 |
| lazy_delta | argument | 684,531 | 1,394.009 | 877.981 |
| projection | argument | 77,846 | 275.874 | 188.813 |
| quick | binder-domain | 343,910 | 73.551 | 0.153 |
| lazy_delta | dependent-body | 4,313 | 30.717 | 52.950 |
| all exception/fallback rows | other kinds | 209 | 3.143 | 6.069 |

`failure_followup` was zero in every selected row. This means the observed
root's propagation is ordinary recursive descent and reduction continuation,
not repeated immediate retry after a failed child.

## A2: depth and fan-out

The M1 depth distribution reaches bucket 65 (the analyzer's saturated
bucket), with mean bucket 64.791. Its fan-out reaches bucket 28, with mean
1.305 children per M1 call. M2 reaches depth bucket 65 and fan-out bucket 9
(means 53.156 and 1.042); Matched reaches depth bucket 65 and has zero
fan-out in the provenance projection. The high depth and nontrivial fan-out
show a deep and wide tree: long projection/application chains repeatedly
branch into arguments and dependent checks.

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

The dominant projection-to-projection subtree has 2,951,993 child calls and
38,983.983 ms exclusive time. The largest application-argument subtree has
4,542,955 calls and 21,618.337 ms. These are direct branch transitions, not
labels inferred from a bounded event sample.

## Instrumentation validity and overhead

M1/M2/Matched shares are accumulated by the kernel for every comparison in
the selected root. Calls absent from raw enter/exit records are classified by
the same complete comparison object and its parent divergence metadata. The
Cone trace retained 808 entered and 746 exited raw records, while aggregate
coverage was 12,220,818/12,220,818 calls. The transition and per-label
exclusive aggregates are therefore complete; raw records are only for manual
path review. READY4 root wall time was 121.553 s in counters mode and
144.482 s in trace mode. Existing READY3.2 paired controls reported a
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
| O | preserved | 12,220,818 (READY4; 12,220,823 accepted control) | valid baseline |
| O-cut | not demonstrably preserved | not used | rejected: telescope/root changed |
| O-restore | preserved | 12,220,818 | restored baseline |

O and O-restore are the same original source and root operation. No causal
speedup is claimed because no type-correct M0-preserving descendant
replacement was available. This is a limitation of the intervention, not a
substitution of a smaller consumer or a different theorem.
