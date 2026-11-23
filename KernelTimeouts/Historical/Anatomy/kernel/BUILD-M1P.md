# READY4 branch-reason instrumentation build

READY4 extends READY3.2 for Lean 4.35.0 (githash
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Lean 4.33.1 (githash
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). The patch is a type-checker
source patch against each pristine release. It adds branch metadata and
kernel-side aggregates while preserving READY3.2's process-wide atomic root
serial and active-root pinning.

## What is recorded

Each recursive comparison records its initiating parent branch, child kind,
argument/field/binder index, reduction-before-child flag, reduced side,
exposed definition/projection, child result, and failure-followup flag. The
comparison object also maintains complete transition totals and depth/fanout
histograms. JSONL enter/exit and reduction records remain bounded by
`LEAN_DEFEQ_MPRWE_MAX_EVENTS`; a mutex protects the process-wide stream from
multi-threaded line interleaving.

## Instrumentation validity caveat (§1.2)

M0/M1/M2/Matched time shares are accumulated over **all calls** in the active
root by the kernel's comparison objects and aggregate maps. They are not
inferred from bounded raw enter/exit records. A call absent from raw capture
still receives its provenance label from its expression hashes and parent
divergence/reduction state; if that evidence is insufficient it remains
`Unclassified`. The per-label exclusive-time aggregates and transition matrix
are therefore complete over the root. Raw coverage is reported separately
for manual inspection. In the full Cone run, for example, raw coverage was
808 entered calls while aggregate coverage was 12,220,818/12,220,818 calls.

The top transition rows were manually checked against the exact source
branches in `M1P-KERNEL.md`: application function/argument congruence,
projection descent, lazy-delta/WHNF exposure, dependent bodies, and
proposition types. No unknown branch exceeded 5% of root time.

## Build and analysis

Build the patched source with the normal release CMake configuration and
copy the resulting stage-1 `lean` binary to a separate READY4 directory.
Run a detailed trace with:

```sh
LEAN_DEFEQ_ANATOMY=trace \
LEAN_DEFEQ_MPRWE_EVENTS=<events.jsonl> \
LEAN_DEFEQ_MPRWE_MAX_EVENTS=2000 \
lake env bash <current-lean.sh> <ready4-lean> <probe.lean>
```

Analyze complete aggregate rows and the selected process-wide root with:

```sh
python3 mprwe_analyze.py <events.jsonl> --root <root-id>
```

Counters mode is used for broad coverage; detailed trace mode is used for
manual path reconstruction. The patch contains no synchronous hot-path
printing and no change to conversion semantics.

## Validation summary

* Lean 4.35.0 NativePullTensor: root 2,685,580 calls; M1 98.051%, M2
  0.326%, Matched 1.623%; complete transition edges 2,685,579.
* Lean 4.33.1 full Derived-Completion Cone: READY4 root 12,220,818 calls;
  M1 99.685%, M2 0.064%, Matched 0.251%; complete transition edges
  12,220,817. READY3.2's accepted control is 12,220,823 calls; the
  five-call difference is recorded in the Cone report as timeout-boundary
  drift under added observational bookkeeping. READY4 counters and trace
  agree with each other.

Root wall measurements are reported with the validation reports. They are
paired measurements, not normalized overhead claims, because the historical
Cone rebuild and timeout boundary differ from the READY3.2 control runs.
For the current Native probe, a separate no-instrumentation 4.35 binary
completed in 262.87 s process wall but emitted no root counter; that result is
therefore retained as an explicit baseline observation rather than used for a
misleading root-span ratio.
