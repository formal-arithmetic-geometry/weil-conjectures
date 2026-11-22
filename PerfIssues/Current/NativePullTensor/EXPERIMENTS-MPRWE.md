# Mismatch Provenance and Recursive Workload Report

Case: NativePullTensor
Lean / mathlib: Lean 4.35.0, current-case revision 2e92d5989ff; earlier
root measurements used the available READY2 olean snapshot.
Root conversion: the two `Exists.choose` dependent domains in
`nativePullTotalTensor`.
Source snapshots: `OriginalRoot`, `MatchedFunctorObj`, `RestoredRoot` in
`probes/mprwe/`. Instrumentation: READY2 counters/trace; no READY3 was
available.

## 1. Root mismatch

The root pair is `Functor.obj`/`Functor.obj` at the endpoint object. Arguments
0--3 agree; provider argument 4 is the first recorded representation
divergence. The full serialized expressions and local-context identity are
not present in READY2 output. This is the established IM root, not a new
trigger investigation.

## 2. Matched baseline

Baseline level: **A3 diagnostic**, with an A1-like endpoint scope. The regular
provider wrapper keeps the same operation family and non-identical operands;
its direct comparison was 1 ms (earlier IM measurement), but it is not the
full root conversion. The abbreviation-provider pair was 14,134 ms, showing
that provider representation is material. Same root/consumer/telescope: No.
Nontrivial DefEq: Yes for the regular wrapper; recursive counters were below
the reporting threshold. The baseline is therefore supporting evidence only.

## 3. Provenance distribution

The earlier READY2 trace root had 2,685,580 calls, 15,349.294 ms exclusive
comparison, 7,455.561 ms exclusive reduction, depth 81, and 32,060 proposition
comparisons. READY2 has no parent call IDs or reduction event links.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 2,685,579 recursive calls (inferred) | 15,349.294 ms measured total | 100% of attributable trace |

Branch totals (projection 6,968.879 ms; application 2,962.438 ms; lazy delta
2,469.209 ms) are orthogonal branch totals and are not provenance labels.
Dependent comparison/reduction was 10,288.544/5,580.792 ms and proposition
comparison/reduction 5,060.748/1,874.769 ms; these overlap the root categories.

## 4. Newly exposed divergences

The two endpoint domains have similar `Functor.obj` paths, but the trace has
no pair identity or reduction history, so shared M2 descendants cannot be
established. No M2 node is claimed.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier IM root: 22,804.855 ms, 2,685,580 calls. |
| O1/O2/O12/O-all | Unavailable: the only type-correct replacement (`MajorAlignment`) changes provider argument 4 at the root and removes M0. |
| R | Earlier restoration of the endpoint mismatch: 11,363 ms direct endpoint comparison. It restores M0 but is not a selective descendant control. |

The root obligation is preserved in O/R. The aligned endpoint is an invalid C
control because its root no longer contains the provider mismatch. No calls can
be attributed as disappearing from a valid C intervention.

The restored source snapshot keeps the original declaration context; the R
number is the earlier direct pair restoration recorded by the meta probe, not a
library rewrite.

## 6. Conclusion

Matched intrinsic cost is demonstrated for the regular-provider diagnostic
(1 ms) but its full-root share is unknown. M1, M2, and matched descendant
shares are Unclassified. The restored endpoint reproduces the expensive
provider-sensitive comparison, which supports a mismatch-sensitive effect, but
does not distinguish inherited from newly exposed work. Outcome **E** pending
READY3 parent/path instrumentation; no claim of a mismatch cascade is made.

## MPRWE round 2 (superseded historical table)

## MPRWE round 4 (READY3.2; supersedes earlier tables)

Fresh O root 18506 matched between counters and trace: 2,685,580 calls.
Counter comparison-exclusive time was 16,554.296 ms; trace comparison-exclusive
time was 20,949.497 ms (trace reduction 8,525.009 ms). Analyzer READY3.2.
Aggregate records are complete; raw selected-root coverage was 0/2,685,580.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.012 | 0.000% |
| M1 | 1,120,689 | 20,557.669 | 98.126% |
| M2 | 12,041 | 63.186 | 0.302% |
| Matched | 1,552,849 | 328.630 | 1.569% |
| Unclassified | 0 | 0.000 | 0.000% |

Manual top-five aggregate nodes: M1 paths have 5652.486, 5536.010, 2822.583,
2785.109, and 984.085 ms; M2 paths have 18.431, 17.056, 9.040, 7.704, and
3.033 ms; Matched paths have 88.590, 88.306, 47.021, 44.014, and 16.208 ms.
M0 is the root entry. C is invalid because provider alignment changes the root
obligation and no descendant-only alignment type-checks. Outcome: D.

READY3.1-4.35.0 fresh counter and trace runs completed with the original
probe. The selected root had 2,685,580 calls, depth 81, and 20,675.658 ms
aggregate comparison-exclusive time. Aggregate records partition that full
time; the 4,000 raw-event cap was consumed by earlier roots, so this selected
root has 0 raw calls, but its aggregate path records are complete.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.011 | 0.000% |
| M1 | 1,120,689 | 20,287.000 | 98.124% |
| M2 | 12,041 | 61.836 | 0.299% |
| Matched | 1,552,849 | 326.811 | 1.581% |
| Unclassified | 0 | 0.000 | 0.000% |

The two `Exists.choose` domains have the same high-cost M2 paths at
`binder_domain[0]/argument[2]/argument[6]` and
`binder_domain[0]/argument[3]/argument[7]`; the corresponding matched paths
are much larger in calls but remain only 1.6% of exclusive time. This answers
the domain question: the M2 paths are structurally parallel, while the cost
is inherited M1 work. The top M2 and Matched aggregate groups were manually
reviewed by path; no distinct high-cost M2 subtree was found.

The only available C source replacement changes the provider at the root and
removes M0, so it is invalid for C1. No type-correct descendant-only M2
alignment was found. O and R source snapshots are byte-identical; the earlier
R endpoint timing was 11,363 ms. Thus no causal C speedup is claimed and the
restoration is consistent with the original mismatch. Outcome: **C** (M1
dominates; M2 and Matched are measured and small).

## MPRWE round 3 (READY3.2; superseded historical table)

The accepted unmixed root is M1 98.124%, M2 0.299%, Matched 1.581%,
Unclassified 0.000%. The earlier 2.3%/93.6% validation is superseded by the
process-wide root-ID correction.
