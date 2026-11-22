# Mismatch Provenance and Recursive Workload Report

Case: PR1625-TensorSheaf
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; earlier IM/AD
measurements with READY2-4.35.0.
Root: `leftDerivedUpperStarTensorComparison_app_app_fac`, nested outer/inner
`NatTrans.app` dependent equality.
Snapshots: `OriginalNestedApp`, `MatchedNestedApp`, `AlignedNestedApp`,
`RestoredNestedApp` in `probes/mprwe/`.

## 1. Root mismatch

Outer and inner heads are `NatTrans.app`. The established first divergence is
the outer major argument 6; the inner application and `CategoryStruct.comp`
descendants remain in the consumer. Full expressions are unavailable in the
READY2 root record.

## 2. Matched baseline

Baseline level: **A1 diagnostic**. `MatchedNestedApp` retains both application
layers and the dependent result type but aligns the major premise. The direct
matched application was below the timer threshold (reported as 0 ms), so no
nontrivial full-root call count is available. It is not A0 because the aligned
major premise changes the original root mismatch.

## 3. Provenance distribution

Earlier O root: 11,757,788 calls, depth 125, 59,140.866 ms comparison-exclusive
and 55,099.415 ms reduction-exclusive. Trace pair sample: 3,284,552 distinct,
1,715,448 repeated; no parent IDs or contexts.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 11,757,787 recursive calls (inferred) | 59,140.866 ms measured total | 100% of attributable trace |

Dependent comparison/reduction was 45,167.426/45,028.549 ms. Proposition
timers overlap the recursive tree and are not additive.

## 4. Newly exposed divergences

The source retains nested `.app` and projection paths, but no reduction-history
link connects an exposed child to a distinct M2 divergence. M2 is therefore
Unclassified rather than inferred from head names.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier IM root: 114,240.281 ms, 11,757,788 calls. |
| O1/O2/O12/O-all | Invalid/unavailable. `AlignedNestedApp` aligns the outer major argument and removes M0; no child-only replacement type-checks under the same telescope. |
| R | Earlier restored direct nested application: 109,892 ms. M0 is restored, but this is not a selective descendant intervention. |

## 6. Conclusion

The matched diagnostic is cheap, whereas the nested original/restored roots are
about 110--114 s. The inner `.app` is intrinsically nontrivial in isolation,
so the evidence supports mixed interaction (Outcome **D**) but not a measured
M1/M2 split. All recursive provenance remains Unclassified under READY2.
The restored source snapshot retains the declaration context; the R timing is
the earlier direct pair restoration from the meta probe.

## MPRWE round 2

READY3.1-4.35.0 fresh counter and trace runs completed. The selected original
root had 11,757,788 calls, depth 125, and 68,508.492 ms aggregate
comparison-exclusive time. No raw calls from this root survived the cap, but
aggregate records partition the complete time.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.615 | 0.001% |
| M1 | 8,111,028 | 68,146.125 | 99.471% |
| M2 | 4,686 | 48.891 | 0.071% |
| Matched | 3,642,041 | 312.109 | 0.456% |
| Unclassified | 32 | 0.753 | 0.001% |

The outer `.app` entry is cheap; the large descendant groups are M1
continuations through the nested `.app`/projection telescope. The largest M2
path is `binder_body[15]/argument[1]/argument[0]/argument[6]/argument[0]`,
with 48.009 ms, while the corresponding matched group is 309.686 ms. This
is a small M2 contribution and a small intrinsic matched contribution beside
the M1 workload; no additional mismatch layer is cost-dominant.

The outer-major replacement changes the root telescope and removes M0, so it
is invalid for C. No descendant-only M2 alignment type-checks under the same
dependent obligation. O and R snapshots are byte-identical; the earlier R
timing was 109,892 ms. Outcome: **C**.

## MPRWE round 3 (READY3.2)

Shares are M1 99.471%, M2 0.071%, Matched 0.456%, Unclassified 0.001%.
The outer-major alignment remains root-changing and invalid for C.
