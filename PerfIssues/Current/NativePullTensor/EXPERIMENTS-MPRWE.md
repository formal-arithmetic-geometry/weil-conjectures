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
