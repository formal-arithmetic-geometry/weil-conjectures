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
