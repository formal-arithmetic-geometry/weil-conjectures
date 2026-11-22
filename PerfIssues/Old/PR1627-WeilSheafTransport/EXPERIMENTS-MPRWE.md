# Mismatch Provenance and Recursive Workload Report

Case: PR1627-WeilSheafTransport
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; earlier IM/AD
measurements with READY2-4.35.0.
Root: generated `powFunctor` fields and their dependent `id` proof domains.

## 1. Root mismatch

The generated `frobeniusPowIso` field is the first structural divergence in the
dependent generated-field path. The three generated fields have distinct
costs; READY2 does not preserve their parent paths in the root trace.

## 2. Matched baseline

`MatchedGeneric` is **A3 diagnostic**: a same-provider generated field compared
with an `id`-wrapped construction. It is non-structural, both sides
kernel-check, and measured 0.009 ms, one call, depth 0 (earlier IM round 2).
It does not preserve the `powFunctor` dependent telescope.

## 3. Provenance distribution

Earlier O trace root: 10,904,899 calls, 23,911.980 ms comparison-exclusive,
16,853.556 ms reduction-exclusive, depth 61; 1,844,240 distinct and 3,155,760
repeated pairs. The root also had 912 proposition comparisons and no Pi-domain
events. Parent IDs and reduction exposure records are absent.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 10,904,898 recursive calls (inferred) | 23,911.980 ms measured total | 100% of attributable trace |

## 4. Newly exposed divergences

The generated proof prefixes and dependent `id` domains are separately
identified in the source snapshots, but no new divergence can be tied to a
reduction event. No M2 claim is made from repeated-pair counts.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier root: 29,453.890 ms, 10,904,899 calls. |
| O1/O2/O12/O-all | Invalid/unavailable. `AlignedGeneratedFields` changes generated providers/domains and removes the root mismatch; no child-only intervention type-checks. |
| R | Earlier restored generated-field source restores the original expensive fields; no separately measured selective restoration. |

The aligned source emitted no root above 100 ms, but it is not a valid C
control because M0 is gone.

## 6. Conclusion

The constructor diagnostic is cheap, while generated dependent fields are
expensive. This supports an interaction between dependent context and mismatch
work, Outcome **D/E**, with no defensible M1/M2 split under READY2.
The restored source snapshot retains the original declaration context; the R
source is included for replay, but no separate selective restoration timing was
available.

## MPRWE round 2 (superseded historical table)

## MPRWE round 4 (READY3.2; supersedes earlier tables)

Fresh O root 15228 matched between counters and trace: 10,904,899 calls.
Counter/trace comparison-exclusive times were 22,866.272 / 30,919.746 ms;
trace reduction was 27,558.270 ms. Analyzer READY3.2; aggregate records are
complete. Raw coverage was 187,782/10,904,899 calls (1.7%; 1,108.579 ms).
Final source diagnostics occurred after the selected root.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.041 | 0.000% |
| M1 | 2,619,482 | 20,627.197 | 66.712% |
| M2 | 1,512,663 | 7,046.801 | 22.789% |
| Matched | 6,772,753 | 3,245.707 | 10.495% |
| Unclassified | 0 | 0.000 | 0.000% |

Manual top-five aggregate paths under the generated-field body: M1
5600.191, 5090.047, 3573.112, 3498.938, 2861.415 ms; M2 1972.574,
1521.221, 1245.415, 1176.906, 1129.421 ms; Matched 873.394, 744.055,
685.312, 492.219, 450.666 ms. M0 is the root entry. The aligned control
preserves the outer root; restored source retains the original context.

C is valid for this case: aligned and restored controls both preserve the
10,904,899-call root. The aligned control measured 27,417.480 ms with shares
M1 65.9%, M2 25.1%, Matched 9.0%; the restored control measured 26,371.827 ms
with shares M1 64.3%, M2 26.1%, Matched 9.6%. Neither descendant alignment
reduces M2 exposure; the share increases slightly, so the control does not
support an M2-causal reduction. Outcome: D.

